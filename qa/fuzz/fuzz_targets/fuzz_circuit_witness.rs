//! Fuzz `Circuit::witness` pipeline correctness against a native oracle.
//!
//! Drives two reference circuits — `SquareCircuit { times }` and
//! `MySimpleCircuit` — with fuzzer-chosen witnesses, and checks pairwise
//! consistency across three pipelines:
//!
//! 1. **Native spec**: a plain Rust function computing each circuit's
//!    output directly from the witness, no driver involved.
//! 2. **Simulator synthesis**: `circuit.witness(&mut Simulator, w)`; the
//!    `Simulator` driver enforces every gate identity inline, then exposes
//!    each output `Element`'s witness value.
//! 3. **Trace + assembly**: `circuit.trace(w)` produces a `Trace`, then
//!    `Registry::assemble_with_alpha` writes it to a sparse polynomial.
//!
//! ## Invariants enforced
//!
//! - **Synthesis correctness**: the Simulator output values equal the
//!    native spec. Catches bugs in any `Circuit::witness` impl that
//!    produces a non-spec output from a satisfying witness, and catches
//!    gadget plumbing bugs that would emit a constraint inconsistent
//!    with the witness it returns.
//! - **Trace-pipeline implication**: if `Simulator::simulate` accepted,
//!    `circuit.trace` must also return `Ok`. The reverse direction does
//!    *not* hold — `trace::eval`'s `enforce_zero` and `gate` are pure
//!    recorders, not constraint checkers (see `trace.rs:226-261`), so an
//!    unsatisfying witness produces `Err` from `Simulator` and `Ok` from
//!    `trace::eval` by design. Constraint checking is the Simulator's
//!    job; trace's job is to record values for later assembly into a
//!    polynomial whose algebraic identity is checked downstream.
//! - **`alpha` injection contract**: assembling the same trace twice with
//!    distinct `alpha_a` and `alpha_b` produces two polynomials that
//!    differ in exactly one coefficient position, with the difference
//!    equal to `alpha_a - alpha_b`. `Registry::assemble_with_alpha`
//!    documents that `alpha` is written to `a[0]` and used nowhere else;
//!    this catches any future regression that leaks `alpha` into another
//!    slot (which would break commit-blinding / point-at-infinity
//!    protection).
//!
//! ## Circuit coverage
//!
//! `SquareCircuit` exercises a single gadget (`Element::square`) in a
//! parameterized loop. `MySimpleCircuit` exercises `Element::square`,
//! `Element::mul`, `Element::add`, `Element::sub`, and an explicit
//! `Driver::enforce_zero` constraint over a two-element witness with a
//! two-element output. Together they cover most of `Element`'s arithmetic
//! surface.
//!
//! TODO(issue #709): broaden circuit coverage by adding purpose-built
//! reference circuits and another `CircuitChoice` arm for each:
//! - **Boolean**: `Boolean::alloc`, `Boolean::not`, `Boolean::and`,
//!   `conditional_select`. A reference circuit could allocate `n`
//!   booleans from witness bits and assert a target value reconstructed
//!   from them.
//! - **Point**: `Point::alloc`, `endo`, `negate`, `double`,
//!   `conditional_endo`, `conditional_negate`, `add_incomplete`. A
//!   reference circuit could compute a Pasta scalar multiplication of a
//!   fuzzer-chosen base by a fuzzer-chosen scalar and compare to native.
//!   (`fuzz_endoscalar` already does the gadget-level differential; the
//!   gap is exercising it through `Circuit::witness` end-to-end.)
//! - **Routines / sub-circuits**: `Driver::routine`, the
//!   `Routine::predict`/`Routine::execute` split. A reference circuit
//!   could invoke a non-trivial `Routine` impl from
//!   `ragu_testing::routines` and assert its `Aux<'_>` matches the
//!   prediction.
//! - **Multi-stage circuits**: `StageBuilder`, `MultiStage`,
//!   `MultiStageCircuit`. This is the Tier-3B Layer 4 work flagged in
//!   `fuzzing-follow-up-work.md`; needs an `Arbitrary` impl that builds
//!   a stage chain with varying wire counts per stage.
//!
//! ## What this does not catch (deferred — issue #709)
//!
//! The full algebraic identity from `tests/mod.rs:158-187` —
//! `a.revdot(b) == circuit.ky(instance, y)` where
//! `b = r + r.dilate(z) + obj.sy(y, &plan) + Rank::tz(z)` — is the
//! strongest oracle for the synthesis layer and the algebraic bridge
//! between this target (witness-driver side) and `fuzz_sxy_agreement`
//! (wiring/constraint side). Its construction requires
//! `WiringObject::sy` and `Rank::tz`, both `pub(crate)` in
//! `ragu_circuits`, so it is deferred to a separate `unstable-fuzzing`-
//! gated target.

#![no_main]

use arbitrary::Arbitrary;
use core::cell::OnceCell;
use ff::Field;
use ff::PrimeField;
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_circuits::{
    Circuit, CircuitExt,
    polynomials::TestRank,
    registry::{CircuitIndex, Registry, RegistryBuilder},
};
use ragu_core::maybe::Maybe;
use ragu_primitives::Simulator;
use ragu_testing::circuits::{MySimpleCircuit, SquareCircuit};
use std::sync::LazyLock;

#[derive(Arbitrary, Debug)]
enum CircuitChoice {
    /// `SquareCircuit { times }` over a single-Fp witness.
    Square {
        times: u8,
        witness_seed: u64,
        use_special: Option<u8>,
    },
    /// `MySimpleCircuit` over a `(Fp, Fp)` witness. The circuit's internal
    /// constraint is `a^5 == b^2`; many randomly chosen `(a, b)` pairs will
    /// not satisfy it (drivers will reject). The `derive_b_from_a` mode
    /// picks `b = sqrt(a^5)` so the witness is always satisfying.
    Simple {
        a_seed: u64,
        b_seed: u64,
        use_special_a: Option<u8>,
        derive_b_from_a: bool,
    },
}

#[derive(Arbitrary, Debug)]
struct Input {
    circuit: CircuitChoice,
    alpha_a_seed: u64,
    alpha_b_seed: u64,
}

/// Edge-case field elements that exercise boundary behavior.
fn special_value(idx: u8) -> Fp {
    match idx % 8 {
        0 => Fp::ZERO,
        1 => Fp::ONE,
        2 => -Fp::ONE,
        3 => Fp::TWO_INV,
        4 => Fp::ROOT_OF_UNITY,
        5 => Fp::MULTIPLICATIVE_GENERATOR,
        6 => Fp::from(1u64 << 32),
        _ => Fp::from(u64::MAX),
    }
}

/// Per-`times` registry cache for `SquareCircuit`. Building a registry
/// runs the floor planner over `times` squarings — comfortably more
/// expensive than the per-input checks. Memoizing across inputs turns
/// the hot path into trace + assemble after each distinct `times` is
/// observed once. Mirrors the cache in `fuzz_sxy_agreement.rs:42-69`.
struct SquareRegistryCache {
    slots: [OnceCell<Result<Registry<'static, Fp, TestRank>, ()>>; 120],
}

// SAFETY: libfuzzer runs the fuzz target on a single thread, so the
// interior-mutable `OnceCell` slots are never accessed concurrently.
// `LazyLock` requires `Sync` to compile.
unsafe impl Sync for SquareRegistryCache {}

static SQUARE_REGISTRY_CACHE: LazyLock<SquareRegistryCache> =
    LazyLock::new(|| SquareRegistryCache {
        slots: [const { OnceCell::new() }; 120],
    });

fn square_registry_for(times: usize) -> Option<&'static Registry<'static, Fp, TestRank>> {
    debug_assert!((1..=120).contains(&times));
    SQUARE_REGISTRY_CACHE.slots[times - 1]
        .get_or_init(|| {
            let circuit = SquareCircuit { times };
            RegistryBuilder::<Fp, TestRank>::new()
                .register_circuit(circuit)
                .and_then(|b| b.finalize())
                .map_err(|_| ())
        })
        .as_ref()
        .ok()
}

/// `MySimpleCircuit` takes no parameters, so a single global memoized
/// registry suffices.
static SIMPLE_REGISTRY: LazyLock<Option<Registry<'static, Fp, TestRank>>> = LazyLock::new(|| {
    RegistryBuilder::<Fp, TestRank>::new()
        .register_circuit(MySimpleCircuit)
        .and_then(|b| b.finalize())
        .ok()
});

/// Native spec for `SquareCircuit`: compute `w^(2^times)` by repeated
/// squaring directly in the field.
fn square_native(witness: Fp, times: usize) -> Fp {
    let mut acc = witness;
    for _ in 0..times {
        acc = acc.square();
    }
    acc
}

/// Native spec for `MySimpleCircuit`. Returns:
/// - `Some((c, d))` if the witness satisfies `a^5 == b^2`, with
///    `c = a + b`, `d = a - b`.
/// - `None` if the witness violates the constraint; both `Simulator` and
///    `trace::eval` must reject.
fn simple_native(a: Fp, b: Fp) -> Option<(Fp, Fp)> {
    let a5 = a.pow_vartime([5u64]);
    let b2 = b.square();
    if a5 != b2 {
        return None;
    }
    Some((a + b, a - b))
}

/// Try to compute `b = sqrt(a^5)` so that `(a, b)` is a satisfying witness
/// for `MySimpleCircuit`. Returns `None` if `a^5` is a non-residue.
fn derive_satisfying_b(a: Fp) -> Option<Fp> {
    Option::<Fp>::from(a.pow_vartime([5u64]).sqrt())
}

/// Run the differential alpha-injection check on an assembled trace.
/// Asserts that two assemblies with distinct `alpha`s differ in exactly
/// one coefficient position, by exactly the alpha delta. Returns `()` on
/// success, `None` if either assembly errored (skip the iteration), and
/// panics on a violated invariant.
fn check_alpha_injection(
    registry: &Registry<'_, Fp, TestRank>,
    trace: &ragu_circuits::Trace<Fp>,
    alpha_a: Fp,
    alpha_b: Fp,
) -> Option<()> {
    let idx = CircuitIndex::new(0);
    let poly_a = registry.assemble_with_alpha(trace, idx, alpha_a).ok()?;
    let poly_b = registry.assemble_with_alpha(trace, idx, alpha_b).ok()?;

    let coeffs_a: Vec<Fp> = poly_a.iter_coeffs().collect();
    let coeffs_b: Vec<Fp> = poly_b.iter_coeffs().collect();
    assert_eq!(
        coeffs_a.len(),
        coeffs_b.len(),
        "assemble_with_alpha produced polynomials of different length"
    );

    let mut diff_count = 0usize;
    let mut diff_idx = usize::MAX;
    for i in 0..coeffs_a.len() {
        if coeffs_a[i] != coeffs_b[i] {
            diff_count += 1;
            diff_idx = i;
        }
    }
    assert_eq!(
        diff_count, 1,
        "alpha leaked into {diff_count} coefficient positions (expected 1)"
    );
    assert_eq!(
        coeffs_a[diff_idx] - coeffs_b[diff_idx],
        alpha_a - alpha_b,
        "alpha delta mismatch at coefficient position {diff_idx}"
    );
    Some(())
}

fuzz_target!(|input: Input| {
    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!("{:#?}", input);
        return;
    }

    // Decode shared alpha pair. Differential check needs distinct values.
    let alpha_a = Fp::from(input.alpha_a_seed);
    let alpha_b = Fp::from(input.alpha_b_seed);
    let alphas_distinct = input.alpha_a_seed != input.alpha_b_seed && alpha_a != alpha_b;

    match input.circuit {
        CircuitChoice::Square {
            times,
            witness_seed,
            use_special,
        } => {
            let times = ((times as usize) % 120).max(1);
            let witness: Fp = match use_special {
                Some(idx) => special_value(idx),
                None => Fp::from(witness_seed),
            };
            let registry = match square_registry_for(times) {
                Some(r) => r,
                None => return, // rank-bound exceeded for high `times`
            };
            let circuit = SquareCircuit { times };
            let expected = square_native(witness, times);

            let mut sim_value: Option<Fp> = None;
            let sim_result = Simulator::<Fp>::simulate(witness, |dr, w_just| {
                let cw = circuit.witness(dr, w_just)?;
                let elem = cw.into_output();
                sim_value = Some(*elem.value().take());
                Ok(())
            });

            if sim_result.is_err() {
                // `SquareCircuit` has no `enforce_zero` constraints, so
                // any Simulator rejection here would be a plumbing bug;
                // surface it before returning.
                panic!(
                    "Simulator rejected SquareCircuit witness={witness:?} times={times} \
                     — SquareCircuit has no constraints that could fail"
                );
            }

            let sim_value = sim_value.expect("Simulator Ok without writing value");
            assert_eq!(
                sim_value, expected,
                "SquareCircuit: synthesis output != native w^(2^times): \
                 witness={witness:?}, times={times}, sim={sim_value:?}, expected={expected:?}"
            );

            // Simulator accepted, so trace::eval must accept too (one-way
            // implication; see header docstring).
            let trace = match circuit.trace(witness) {
                Ok(t) => t.into_output(),
                Err(_) => panic!(
                    "trace::eval rejected SquareCircuit witness={witness:?} times={times} \
                     but Simulator accepted — driver disagreement"
                ),
            };

            if alphas_distinct {
                check_alpha_injection(registry, &trace, alpha_a, alpha_b);
            }
        }

        CircuitChoice::Simple {
            a_seed,
            b_seed,
            use_special_a,
            derive_b_from_a,
        } => {
            let a: Fp = match use_special_a {
                Some(idx) => special_value(idx),
                None => Fp::from(a_seed),
            };
            let b: Fp = if derive_b_from_a {
                match derive_satisfying_b(a) {
                    Some(v) => v,
                    None => return, // a^5 is a non-residue; skip
                }
            } else {
                Fp::from(b_seed)
            };

            let registry = match SIMPLE_REGISTRY.as_ref() {
                Some(r) => r,
                None => return,
            };
            let circuit = MySimpleCircuit;
            let expected = simple_native(a, b); // None iff a^5 != b^2

            let mut sim_value: Option<(Fp, Fp)> = None;
            let sim_result = Simulator::<Fp>::simulate((a, b), |dr, w_just| {
                let cw = circuit.witness(dr, w_just)?;
                let (c_elem, d_elem) = cw.into_output();
                sim_value = Some((*c_elem.value().take(), *d_elem.value().take()));
                Ok(())
            });

            // Simulator is the constraint checker. Its accept/reject must
            // match the native prediction (`expected.is_some()`).
            match (expected, sim_result.is_ok()) {
                (None, true) => panic!(
                    "MySimpleCircuit: Simulator accepted unsatisfying witness \
                     a={a:?}, b={b:?} (a^5 != b^2)"
                ),
                (Some(_), false) => panic!(
                    "MySimpleCircuit: Simulator rejected satisfying witness \
                     a={a:?}, b={b:?}"
                ),
                _ => {}
            }

            // trace::eval is a pure recorder; it accepts any witness that
            // can be evaluated, satisfying or not. The required implication
            // is one-way: Simulator accept ⇒ trace accept.
            let trace_result = circuit.trace((a, b));
            if sim_result.is_ok() && trace_result.is_err() {
                panic!(
                    "MySimpleCircuit: Simulator accepted but trace::eval rejected \
                     for a={a:?}, b={b:?} — driver disagreement"
                );
            }

            // Output-value check requires a satisfying witness (Simulator
            // accepted). For unsatisfying witnesses we skip the output check
            // but still exercise assembly if trace::eval recorded values.
            if let Some((expected_c, expected_d)) = expected {
                let (sim_c, sim_d) = sim_value.expect("Simulator Ok without writing value");
                assert_eq!(
                    sim_c, expected_c,
                    "MySimpleCircuit: c output != a+b for a={a:?}, b={b:?}"
                );
                assert_eq!(
                    sim_d, expected_d,
                    "MySimpleCircuit: d output != a-b for a={a:?}, b={b:?}"
                );
            }

            // assemble_with_alpha is a property of the assembly function,
            // independent of whether the underlying witness is satisfying,
            // so we run it on any trace::eval success.
            if let Ok(trace) = trace_result {
                let trace = trace.into_output();
                if alphas_distinct {
                    check_alpha_injection(registry, &trace, alpha_a, alpha_b);
                }
            }
        }
    }
});
