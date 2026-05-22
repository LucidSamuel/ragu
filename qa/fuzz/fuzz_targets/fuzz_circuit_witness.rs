//! Fuzz `Circuit::witness` pipeline correctness against a native oracle.
//!
//! For arbitrary `witness: Fp` and `times: 1..=120`, this target runs
//! `SquareCircuit { times }` through three pipelines and checks pairwise
//! consistency:
//!
//! 1. **Native spec**: compute `w^(2^times)` directly via repeated squaring.
//! 2. **Simulator synthesis**: `circuit.witness(&mut Simulator, w)`; the
//!    `Simulator` driver enforces every gate identity inline, then exposes
//!    the output `Element`'s witness value.
//! 3. **Trace + assembly**: `circuit.trace(w)` produces a `Trace`, then
//!    `Registry::assemble_with_alpha` writes it to a sparse polynomial.
//!
//! ## Invariants enforced
//!
//! - **Synthesis correctness**: the Simulator output value equals the native
//!    `w^(2^times)`. Catches bugs in any `Circuit::witness` impl that
//!    produces a non-spec output from a satisfying witness, and (because
//!    `Simulator::gate` checks `a*b = c` inline) catches `Element::square`
//!    plumbing bugs that would emit a constraint inconsistent with the
//!    witness it returns.
//! - **Trace-pipeline robustness**: `trace::eval` returns `Ok` whenever
//!    Simulator synthesis returned `Ok`. The two drivers must be
//!    observationally equivalent on `Circuit::witness`.
//! - **`alpha` injection contract**: assembling the same trace twice with
//!    distinct `alpha_a` and `alpha_b` produces two polynomials that
//!    differ in exactly one coefficient position, with the difference
//!    equal to `alpha_a - alpha_b`. `Registry::assemble_with_alpha`
//!    documents that `alpha` is written to `a[0]` and used nowhere else;
//!    this catches any future regression that leaks `alpha` into another
//!    slot (which would break commit-blinding / point-at-infinity
//!    protection).
//!
//! ## What this does not catch (deferred — issue #709)
//!
//! The full algebraic identity from `tests/mod.rs:158-187` —
//! `a.revdot(b) == circuit.ky(instance, y)` where
//! `b = r + r.dilate(z) + obj.sy(y, &plan) + Rank::tz(z)` — is the
//! strongest oracle for the synthesis layer. Its construction requires
//! `WiringObject::sy` and `Rank::tz`, both `pub(crate)` in `ragu_circuits`.
//! Exposing them is an `unstable-fuzzing` feature flag away (per
//! `feedback_fuzzing_standards.md`) but was scoped out of this target —
//! see `fuzzing_perf.md` for the upgrade path.

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
use ragu_testing::circuits::SquareCircuit;
use std::sync::LazyLock;

#[derive(Arbitrary, Debug)]
struct Input {
    times: u8,
    witness_seed: u64,
    /// If `Some`, override `witness_seed` with a special edge-case value.
    use_special: Option<u8>,
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

/// Per-`times` registry cache. Building a registry for `SquareCircuit`
/// runs the floor planner over `times` squarings — comfortably more
/// expensive than the per-input checks the fuzz body performs. Memoizing
/// across inputs turns the hot path into trace + assemble + revdot after
/// each distinct `times` is observed once. Mirrors the cache in
/// `fuzz_sxy_agreement.rs:42-69`.
struct RegistryCache {
    /// Slot for `times = i + 1`, indexed 0..119.
    slots: [OnceCell<Result<Registry<'static, Fp, TestRank>, ()>>; 120],
}

// SAFETY: libfuzzer runs the fuzz target on a single thread, so the
// interior-mutable `OnceCell` slots are never accessed concurrently.
// `LazyLock` requires `Sync` to compile.
unsafe impl Sync for RegistryCache {}

static REGISTRY_CACHE: LazyLock<RegistryCache> = LazyLock::new(|| RegistryCache {
    slots: [const { OnceCell::new() }; 120],
});

fn registry_for(times: usize) -> Option<&'static Registry<'static, Fp, TestRank>> {
    debug_assert!((1..=120).contains(&times));
    REGISTRY_CACHE.slots[times - 1]
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

/// Native spec: compute `w^(2^times)` by repeated squaring.
fn native_expected(witness: Fp, times: usize) -> Fp {
    let mut acc = witness;
    for _ in 0..times {
        acc = acc.square();
    }
    acc
}

fuzz_target!(|input: Input| {
    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!("{:#?}", input);
        return;
    }

    let times = ((input.times as usize) % 120).max(1);

    let witness: Fp = match input.use_special {
        Some(idx) => special_value(idx),
        None => Fp::from(input.witness_seed),
    };

    // Skip if registry build fails (rank-bound exceeded for high `times`).
    let registry = match registry_for(times) {
        Some(r) => r,
        None => return,
    };

    let circuit = SquareCircuit { times };

    // Oracle: native spec.
    let expected = native_expected(witness, times);

    // Synthesis via Simulator. The driver checks each `a * b = c` gate
    // inline; the closure's return value is discarded by `Simulator::simulate`,
    // so the synthesized output escapes through a captured mutable variable.
    let mut sim_value: Option<Fp> = None;
    let sim_result = Simulator::<Fp>::simulate(witness, |dr, w_just| {
        let cw = circuit.witness(dr, w_just)?;
        let elem = cw.into_output();
        sim_value = Some(*elem.value().take());
        Ok(())
    });

    if sim_result.is_err() {
        // Simulator rejected — under SquareCircuit this only happens via
        // gate-plumbing bugs. We still want the test to surface that, so
        // assert that the trace pipeline also rejects (drivers must agree).
        assert!(
            circuit.trace(witness).is_err(),
            "Simulator rejected witness {witness:?} at times={times} but \
             trace::eval accepted — model/real driver disagreement"
        );
        return;
    }

    let sim_value = sim_value.expect("Simulator simulate returned Ok without writing value");
    assert_eq!(
        sim_value, expected,
        "synthesis output != native w^(2^times): witness={witness:?}, times={times}, \
         sim={sim_value:?}, expected={expected:?}"
    );

    // Trace must agree on accept/reject with Simulator. We already returned
    // above on the Err path; here, both Ok.
    let trace = match circuit.trace(witness) {
        Ok(t) => t.into_output(),
        Err(_) => panic!(
            "trace::eval rejected witness {witness:?} at times={times} \
             but Simulator accepted — model/real driver disagreement"
        ),
    };

    // Assembly correctness: alpha is written to a[0] and nowhere else. Two
    // assemblies with distinct alphas should differ in exactly one
    // coefficient position by exactly the alpha delta.
    if input.alpha_a_seed == input.alpha_b_seed {
        return; // need distinct alphas for the differential check
    }
    let alpha_a = Fp::from(input.alpha_a_seed);
    let alpha_b = Fp::from(input.alpha_b_seed);
    if alpha_a == alpha_b {
        return; // both seeds map to the same Fp (e.g., via reduction)
    }

    let idx = CircuitIndex::new(0);
    let poly_a = match registry.assemble_with_alpha(&trace, idx, alpha_a) {
        Ok(p) => p,
        Err(_) => return,
    };
    let poly_b = match registry.assemble_with_alpha(&trace, idx, alpha_b) {
        Ok(p) => p,
        Err(_) => return,
    };

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
        "alpha leaked into {diff_count} coefficient positions (expected 1) \
         at times={times}, witness={witness:?}"
    );
    assert_eq!(
        coeffs_a[diff_idx] - coeffs_b[diff_idx],
        alpha_a - alpha_b,
        "alpha delta mismatch at coefficient position {diff_idx}"
    );
});
