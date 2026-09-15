//! Check the production base-case sign and both collapse guards for all
//! combinations of trivial and nontrivial child headers.

use alloc::{vec, vec::Vec};

use proptest::prelude::*;
use ragu_arithmetic::{
    Coeff, Cycle, FixedGenerators,
    ff::Field,
    group::{Curve, CurveAffine},
};
use ragu_backend::{Backend, ReferenceBackend};
use ragu_circuits::{
    Circuit,
    polynomials::{Rank, sparse},
    staging::MultiStage,
};
use ragu_core::{
    Result,
    drivers::{Driver, DriverTypes, LinearExpression},
    gadgets::Bound,
    maybe::Empty,
    routines::Routine,
};
use ragu_pasta::{EqAffine, Fp, Fq};
use ragu_primitives::{GadgetExt, io::Write};
use ragu_testing::strategies;

use super::recursive_propagation_tests::support::{
    self, C, HEADER_SIZE, Merge, R, Seed, TrivialLeft, TrivialRight, Value,
};
use crate::{
    internal::{
        native,
        nested::{self, stages::challenges},
        stage_wires::{StageReader, stage_wire_indices, wire_degree, wires_of},
    },
    step::internal::trivial::Trivial,
};

fn check_signs(app: &support::App, inputs: &support::Inputs) -> Result<()> {
    let mut rng = inputs.prover_rng();
    let unit = app.seed(&mut rng, Trivial::new(), ())?.0;
    let left = app.seed(&mut rng, Seed::new(), inputs.left)?.0;
    let right = app.seed(&mut rng, Seed::new(), inputs.right)?.0;
    assert_ne!(left.data(), right.data());
    let cases = [
        (
            "both",
            true,
            app.fuse(
                &mut rng,
                Seed::new(),
                inputs.salt,
                unit.clone(),
                unit.clone(),
            )?
            .0,
        ),
        (
            "left",
            false,
            app.fuse(
                &mut rng,
                TrivialLeft::new(),
                inputs.salt + Fp::ONE,
                unit.clone(),
                right.clone(),
            )?
            .0,
        ),
        (
            "right",
            false,
            app.fuse(
                &mut rng,
                TrivialRight::new(),
                inputs.salt + Fp::from(2),
                left.clone(),
                unit,
            )?
            .0,
        ),
        (
            "neither",
            false,
            app.fuse(
                &mut rng,
                Merge::new(),
                inputs.salt + Fp::from(3),
                left.clone(),
                right,
            )?
            .0,
        ),
    ];
    let sign_wire = stage_wire_indices::<_, R, challenges::Stage<EqAffine, R>>(|stage| {
        wires_of(&stage.base_case.lift)
    })?[0];
    for (case, base_case, honest) in cases {
        assert!(
            app.verify(&honest, inputs.verifier_rng())?,
            "{case}: honest proof"
        );
        let sign = if base_case { Fq::ONE } else { -Fq::ONE };
        let (mut changed, data) = honest.clone().into_parts();
        assert_eq!(
            StageReader::new(&changed.nested_challenges_rx).read(sign_wire),
            sign
        );

        // Flip the sign and repair both the stage commitment and its exported
        // partial. The native binder must still derive the sign from the headers.
        support::set_wires(&mut changed.nested_challenges_rx, &[sign_wire], &[-sign]);
        changed.nested_challenges_commitment.0 = ReferenceBackend::sparse_commit_to_affine(
            &changed.nested_challenges_rx,
            C::nested_generators(app.params),
        );
        let delta = -sign - sign;
        let generator = C::nested_generators(app.params).g()[wire_degree::<R>(sign_wire)];
        changed.nested_challenges_partial =
            (changed.nested_challenges_partial.to_curve() + generator * delta).to_affine();
        let forged = changed.carry::<Value>(data);
        assert!(
            !app.verify(&forged, inputs.verifier_rng())?,
            "{case}: forged sign"
        );
        for (label, child, expected) in [("honest", &honest, true), ("forged", &forged, false)] {
            for (position, descendant) in support::descendants(app, child, &left, &mut rng)? {
                assert_eq!(
                    app.verify(&descendant, inputs.verifier_rng())?,
                    expected,
                    "{case}/{label}: {position}"
                );
            }
        }
    }
    Ok(())
}

fn native_c_position() -> usize {
    let mut position = 0;
    let mut found = None;
    native::unified::Coverage::default().for_each_slot(|name, _, wires| {
        if name == "c" {
            assert!(found.is_none());
            found = Some(position);
        }
        position += wires;
    });
    found.expect("the native unified instance has a c slot")
}

/// Linear combinations of polynomial coefficients, used only to check the
/// stored collapse traces and locate the guard's `difference = c - computed_c`.
#[derive(Clone)]
struct Expression<F: Field> {
    constant: F,
    terms: Vec<(usize, F)>,
    gain: F,
}

impl<F: Field> Expression<F> {
    fn zero() -> Self {
        Self {
            constant: F::ZERO,
            terms: Vec::new(),
            gain: F::ONE,
        }
    }

    fn wire(degree: usize) -> Self {
        Self {
            terms: vec![(degree, F::ONE)],
            ..Self::zero()
        }
    }

    fn coefficient(&self, degree: usize) -> F {
        self.terms
            .iter()
            .filter(|(i, _)| *i == degree)
            .map(|(_, c)| c)
            .sum()
    }

    fn evaluate(&self, coefficients: &[F]) -> F {
        self.constant
            + self
                .terms
                .iter()
                .map(|&(i, c)| coefficients[i] * c)
                .sum::<F>()
    }
}

impl<F: Field> LinearExpression<Self, F> for Expression<F> {
    fn add_term(mut self, wire: &Self, coefficient: Coeff<F>) -> Self {
        let scale = self.gain * coefficient.value();
        self.constant += wire.constant * scale;
        self.terms
            .extend(wire.terms.iter().map(|&(i, c)| (i, c * scale)));
        self
    }

    fn gain(mut self, coefficient: Coeff<F>) -> Self {
        self.gain *= coefficient.value();
        self
    }
}

/// Evaluate constraints emitted by the production collapse circuits against
/// their stored trace coefficients. The tests supply any coefficient edits.
/// These circuits use a single gate segment; reject routine calls so a future
/// layout change cannot silently misindex the trace.
struct TraceConstraints<F: Field> {
    gates: usize,
    linear: Vec<(usize, Expression<F>)>,
}

impl<F: Field> TraceConstraints<F> {
    fn hold(&self, coefficients: &[F]) -> bool {
        let n = R::n();
        coefficients[4 * n - 1] == F::ONE
            && (1..self.gates).all(|i| {
                let [a, b, c, d] =
                    [2 * n - 1 - i, 2 * n + i, i, 4 * n - 1 - i].map(|degree| coefficients[degree]);
                a * b == c && c * d == F::ZERO
            })
            && self
                .linear
                .iter()
                .all(|(_, equation)| equation.evaluate(coefficients) == F::ZERO)
    }
}

impl<F: Field> DriverTypes for TraceConstraints<F> {
    type ImplField = F;
    type ImplWire = Expression<F>;
    type MaybeKind = Empty;
    type LCadd = Expression<F>;
    type LCenforce = Expression<F>;
    type Extra = usize;

    fn gate(
        &mut self,
        _: impl Fn() -> Result<(Coeff<F>, Coeff<F>, Coeff<F>)>,
    ) -> Result<(Self::ImplWire, Self::ImplWire, Self::ImplWire, usize)> {
        let i = self.gates;
        self.gates += 1;
        assert!(i < R::n());
        Ok((
            Expression::wire(2 * R::n() - 1 - i),
            Expression::wire(2 * R::n() + i),
            Expression::wire(i),
            4 * R::n() - 1 - i,
        ))
    }

    fn assign_extra(
        &mut self,
        degree: usize,
        _: impl Fn() -> Result<Coeff<F>>,
    ) -> Result<Self::ImplWire> {
        Ok(Expression::wire(degree))
    }
}

impl<'dr, F: Field> Driver<'dr> for TraceConstraints<F> {
    type F = F;
    type Wire = Expression<F>;
    const ONE: Self::Wire = Expression {
        constant: F::ONE,
        terms: Vec::new(),
        gain: F::ONE,
    };

    fn add(&mut self, expression: impl Fn(Self::LCadd) -> Self::LCadd) -> Self::Wire {
        expression(Expression::zero())
    }

    fn enforce_zero(
        &mut self,
        expression: impl Fn(Self::LCenforce) -> Self::LCenforce,
    ) -> Result<()> {
        self.linear
            .push((self.gates - 1, expression(Expression::zero())));
        Ok(())
    }

    fn routine<Ro: Routine<F> + 'dr>(
        &mut self,
        _: Ro,
        _: Bound<'dr, Self, Ro::Input>,
    ) -> Result<Bound<'dr, Self, Ro::Output>> {
        panic!("collapse trace check requires a single gate segment")
    }
}

fn accepts_wrong_c<F: Field, Cir: Circuit<F>>(
    circuit: Cir,
    trace: &sparse::Polynomial<F, R>,
    c_position: usize,
    expected_c: F,
    delta: F,
) -> Result<bool>
where
    Cir::Output: Write<F>,
{
    let mut constraints = TraceConstraints {
        gates: 1,
        linear: Vec::new(),
    };
    let (output, _) = circuit.witness(&mut constraints, Empty)?.into_parts();
    let mut instance = Vec::new();
    output.write(&mut constraints, &mut instance)?;
    let c = instance[c_position].wire();
    assert_eq!(c.constant, F::ZERO);
    assert_eq!(c.terms.len(), 1, "c must be a single allocated wire");
    let (c_degree, coefficient) = c.terms[0];
    assert_eq!(coefficient, F::ONE);

    let mut coefficients: Vec<_> = trace.iter_coeffs().collect();
    assert_eq!(coefficients[c_degree], expected_c);
    assert!(
        constraints.hold(&coefficients),
        "honest trace must satisfy the circuit"
    );

    // Locate the one equation that binds c to the guard's B wire. Requiring
    // these coefficients makes a removed guard or changed layout fail loudly.
    let equations: Vec<_> = constraints
        .linear
        .iter()
        .filter(|(_, equation)| equation.coefficient(c_degree) != F::ZERO)
        .collect();
    assert_eq!(equations.len(), 1, "one collapse guard must consume c");
    let (gate, equation) = equations[0];
    let difference = 2 * R::n() + gate;
    assert_eq!(equation.coefficient(c_degree), -F::ONE);
    assert_eq!(equation.coefficient(difference), F::ONE);

    assert_ne!(delta, F::ZERO);
    coefficients[c_degree] += delta;
    assert!(
        !constraints.hold(&coefficients),
        "an unrepaired guard input must fail"
    );
    // Repair only difference = c - computed_c. Every other coefficient stays
    // honest; the remaining condition * difference = 0 must enforce the guard.
    coefficients[difference] += delta;
    Ok(constraints.hold(&coefficients))
}

fn check_guards(
    app: &support::App,
    inputs: &support::Inputs,
    native_delta: Fp,
    nested_delta: Fq,
) -> Result<()> {
    let mut rng = inputs.prover_rng();
    let unit = app.seed(&mut rng, Trivial::new(), ())?.0;
    let left = app.seed(&mut rng, Seed::new(), inputs.left)?.0;
    let right = app.seed(&mut rng, Seed::new(), inputs.right)?.0;
    let cases = [
        (
            "both",
            true,
            app.fuse(
                &mut rng,
                Seed::new(),
                inputs.salt,
                unit.clone(),
                unit.clone(),
            )?
            .0,
        ),
        (
            "left",
            false,
            app.fuse(
                &mut rng,
                TrivialLeft::new(),
                inputs.salt + Fp::ONE,
                unit.clone(),
                right.clone(),
            )?
            .0,
        ),
        (
            "right",
            false,
            app.fuse(
                &mut rng,
                TrivialRight::new(),
                inputs.salt + Fp::from(2),
                left.clone(),
                unit,
            )?
            .0,
        ),
        (
            "neither",
            false,
            app.fuse(
                &mut rng,
                Merge::new(),
                inputs.salt + Fp::from(3),
                left,
                right,
            )?
            .0,
        ),
    ];
    for (case, exempt, pcd) in cases {
        assert!(
            app.verify(&pcd, inputs.verifier_rng())?,
            "{case}: honest proof"
        );
        let proof = pcd.proof();
        let mut native_trace = proof.native_outer_collapse_rx.clone();
        native_trace.add_assign(&proof.native_preamble_rx);
        native_trace.add_assign(&proof.native_outer_error_rx);
        assert_eq!(
            accepts_wrong_c(
                native::circuits::outer_collapse::Circuit::<
                    C,
                    R,
                    HEADER_SIZE,
                    native::RevdotParameters,
                >::new(),
                &native_trace,
                native_c_position(),
                proof.native_c(),
                native_delta,
            )?,
            exempt,
            "{case}: native c guard"
        );

        let mut nested_trace = proof.nested_collapse_rx.clone();
        for stage in [
            nested::RxIndex::EndoscalarStage,
            nested::RxIndex::PointsStage,
            nested::RxIndex::BridgePreamble,
            nested::RxIndex::BridgeSPrime,
            nested::RxIndex::BridgeInnerError,
            nested::RxIndex::BridgeOuterError,
            nested::RxIndex::BridgeAB,
            nested::RxIndex::BridgeQuery,
            nested::RxIndex::BridgeF,
            nested::RxIndex::BridgeEval,
            nested::RxIndex::ChallengeStage,
        ] {
            nested_trace.add_assign(&proof[stage]);
        }
        assert_eq!(
            accepts_wrong_c(
                MultiStage::new(nested::circuits::collapse::Circuit::<EqAffine, R>::new()),
                &nested_trace,
                0, // c_n is the first slot in the nested unified instance.
                proof.nested_c(),
                nested_delta,
            )?,
            exempt,
            "{case}: nested c guard"
        );
    }
    Ok(())
}

proptest! {
    #![proptest_config(support::config())]

    #[test]
    fn mixed_headers_bind_the_base_case_sign(inputs in support::inputs()) {
        support::with_app(|app| check_signs(app, &inputs)).unwrap();
    }

    #[test]
    fn both_collapse_guards_require_both_children_trivial(
        inputs in support::inputs(),
        native_delta in strategies::nonzero_prime_field_element::<Fp>(),
        nested_delta in strategies::nonzero_prime_field_element::<Fq>(),
    ) {
        support::with_app(|app| check_guards(app, &inputs, native_delta, nested_delta)).unwrap();
    }
}
