//! Export circuit for the nested section: pins the nested unified instance
//! to the stages that hold its values.
//!
//! The [`unified`] instance a parent copies into its `preamble` bridge stage
//! is only as good as the circuit that ties it to this step's data. This
//! circuit loads the stages and enforces, wire by wire, that the instance's
//! lifted $x$, $y$ and $u$ are the challenge stage's, and that its exported
//! host-curve commitments are the ones the bridge stages and the points
//! stage hold. $c_n$ and $v_n$ are left to the collapse and `compute_v`
//! circuits, which compute them.
//!
//! Its claim's $k(Y)$ encodes the instance. A parent computes the expected
//! $k(y_n)$ from its own copies. Verifying the parent's nested fold with
//! that expected value binds the copies to the child's exported wires;
//! constructing the fold prover-side only prepares this recursive
//! connection. The export circuit establishes the local instance-to-stage
//! relation, while the parent fold check must enforce the recursive one.
//!
//! This commit removes the copying circuits before the parent's nested
//! fold is checked in-circuit. Direct verification rejects a proof with
//! mismatched exported commitments, but a parent built from that child can
//! still verify. The next commit adds the nested collapse circuit, which
//! computes each child's expected $k(y_n)$ from the preamble copies and
//! constrains both folding layers, closing this temporary enforcement gap.

use core::marker::PhantomData;

use ragu_arithmetic::CurveAffine;
use ragu_circuits::{
    WithAux,
    polynomials::Rank,
    staging::{MultiStageCircuit, StageBuilder},
};
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Kind},
    maybe::Maybe,
};
use ragu_primitives::{GadgetExt as _, allocator::Standard};

use crate::internal::{
    endoscalar::{EndoscalarStage, PointsStage, PointsWitness},
    nested::{NUM_ENDOSCALING_POINTS, stages, unified},
};

/// The witnesses of every stage this circuit reserves, and the instance.
pub struct Witness<'a, C: CurveAffine> {
    pub instance: unified::Instance<C>,
    pub endoscalar: u128,
    pub points: &'a PointsWitness<C, NUM_ENDOSCALING_POINTS>,
    pub preamble: &'a stages::preamble::Witness<C>,
    pub s_prime: &'a stages::s_prime::Witness<C>,
    pub inner_error: &'a stages::inner_error::Witness<C>,
    pub outer_error: &'a stages::outer_error::Witness<C>,
    pub ab: &'a stages::ab::Witness<C>,
    pub query: &'a stages::query::Witness<C>,
    pub f: &'a stages::f::Witness<C>,
    pub eval: &'a stages::eval::Witness<C>,
    pub challenges: &'a stages::challenges::Witness<C::Base>,
    pub beta: stages::beta::Witness<C::Base>,
}

/// Export circuit pinning the nested unified instance to the stages.
pub struct Circuit<C: CurveAffine, R: Rank> {
    _marker: PhantomData<(C, R)>,
}

impl<C: CurveAffine, R: Rank> Circuit<C, R> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}

impl<C: CurveAffine, R: Rank> MultiStageCircuit<C::Base, R> for Circuit<C, R> {
    type Last = stages::beta::Stage<C, R>;
    type Instance<'source> = &'source unified::Instance<C>;
    type Witness<'source> = Witness<'source, C>;
    type Output = Kind![C::Base; unified::Output<'_, _, C>];
    type Aux<'source> = ();

    fn instance<'dr, 'source: 'dr, D: Driver<'dr, F = C::Base>>(
        &self,
        _: &mut D,
        _: DriverValue<D, Self::Instance<'source>>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        unreachable!("instance for internal circuits is not invoked")
    }

    fn witness<'a, 'dr, 'source: 'dr, D: Driver<'dr, F = C::Base>>(
        &self,
        dr: StageBuilder<'a, 'dr, D, R, (), Self::Last>,
        witness: DriverValue<D, Self::Witness<'source>>,
    ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'source>>>> {
        let (endoscalar_guard, dr) = dr.add_stage::<EndoscalarStage>()?;
        let (points_guard, dr) = dr.add_stage::<PointsStage<C, NUM_ENDOSCALING_POINTS>>()?;
        let (preamble_guard, dr) = dr.add_stage::<stages::preamble::Stage<C, R>>()?;
        let (s_prime_guard, dr) = dr.add_stage::<stages::s_prime::Stage<C, R>>()?;
        let (inner_error_guard, dr) = dr.add_stage::<stages::inner_error::Stage<C, R>>()?;
        let (outer_error_guard, dr) = dr.add_stage::<stages::outer_error::Stage<C, R>>()?;
        let (ab_guard, dr) = dr.add_stage::<stages::ab::Stage<C, R>>()?;
        let (query_guard, dr) = dr.add_stage::<stages::query::Stage<C, R>>()?;
        let (f_guard, dr) = dr.add_stage::<stages::f::Stage<C, R>>()?;
        let (eval_guard, dr) = dr.add_stage::<stages::eval::Stage<C, R>>()?;
        let (challenges_guard, dr) = dr.add_stage::<stages::challenges::Stage<C, R>>()?;
        let (beta_guard, dr) = dr.add_stage::<stages::beta::Stage<C, R>>()?;
        let dr = dr.finish();

        // Load shared stage wires without re-emitting their output contracts.
        // Allocating the exported instance below checks its points' curve
        // membership; the equalities transfer those checks to their stage
        // copies. This does not validate all PointsStage entries or the
        // endoscalar bits; those checks follow with the endoscaling contract
        // enforcement.
        let _ = endoscalar_guard.unenforced(dr, witness.as_ref().map(|w| w.endoscalar))?;
        let points = points_guard.unenforced(dr, witness.as_ref().map(|w| w.points))?;
        let preamble = preamble_guard.unenforced(dr, witness.as_ref().map(|w| w.preamble))?;
        let _ = s_prime_guard.unenforced(dr, witness.as_ref().map(|w| w.s_prime))?;
        let inner_error =
            inner_error_guard.unenforced(dr, witness.as_ref().map(|w| w.inner_error))?;
        let outer_error =
            outer_error_guard.unenforced(dr, witness.as_ref().map(|w| w.outer_error))?;
        let ab = ab_guard.unenforced(dr, witness.as_ref().map(|w| w.ab))?;
        let query = query_guard.unenforced(dr, witness.as_ref().map(|w| w.query))?;
        let _ = f_guard.unenforced(dr, witness.as_ref().map(|w| w.f))?;
        let eval = eval_guard.unenforced(dr, witness.as_ref().map(|w| w.eval))?;
        let challenges = challenges_guard.unenforced(dr, witness.as_ref().map(|w| w.challenges))?;
        let _ = beta_guard.unenforced(dr, witness.as_ref().map(|w| w.beta))?;

        let allocator = &mut Standard::new();
        let output = unified::Output::alloc(dr, allocator, witness.as_ref().map(|w| &w.instance))?;

        // The lifted challenges a parent opens this step at.
        output
            .x
            .enforce_equal(dr, &challenges.pairs[stages::challenges::X].lift)?;
        output
            .y
            .enforce_equal(dr, &challenges.pairs[stages::challenges::Y].lift)?;
        output
            .u
            .enforce_equal(dr, &challenges.pairs[stages::challenges::U].lift)?;

        // The commitments a parent endoscales, in `unified` order.
        let last_interstitial = points
            .interstitials
            .last()
            .expect("NUM_ENDOSCALING_POINTS guarantees >= 1 interstitial");
        let exported = [
            &preamble.native_preamble,
            &inner_error.native_inner_error,
            &outer_error.native_outer_error,
            &query.native_query,
            &eval.native_eval,
            &ab.a,
            &ab.b,
            &query.registry_xy,
            last_interstitial,
        ];
        for (instance, stage) in output.exported.iter().zip(exported) {
            instance.enforce_equal(dr, stage)?;
        }

        Ok(WithAux::new(output, D::unit()))
    }
}
