//! Export circuit for the nested section: pins the nested unified instance
//! to the stages that hold its values.
//!
//! The [`unified`] instance a parent copies into its `preamble` bridge stage
//! is only as good as the circuit that ties it to this step's data. This
//! circuit loads the stages and enforces, wire by wire, that the instance's
//! lifted $x$, $y$ and $u$ are the challenge stage's, and that its exported
//! host-curve commitments are the ones the bridge stages and the points
//! stage hold. $c_n$ and $v_n$ are the [`collapse`](super::collapse) and
//! [`compute_v`](super::compute_v) circuits' slots.
//!
//! Its claim's $k(Y)$ encodes the instance. A parent computes the expected
//! $k(y_n)$ from its preamble copies of the child's instance. The parent's
//! [`collapse`](super::collapse) circuit computes this value in-circuit and
//! checks both folding layers, binding the copies to the child's exported
//! wires through the nested accumulator outside the base case. Export
//! establishes the local instance-to-stage relation; collapse enforces its
//! use in the parent's recursive fold.

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
    gadgets::Bound,
    maybe::Maybe,
};
use ragu_primitives::{GadgetExt as _, allocator::Standard};

use super::common;
use crate::internal::nested::{stages, unified};

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
    type Witness<'source> = common::Witness<'source, C>;
    type Output = unified::OutputKind<C>;
    type Aux<'source> = unified::Instance<C>;

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
        // Load shared stage wires without re-emitting their output contracts.
        // Allocating the exported instance below checks its points' curve
        // membership; the equalities transfer those checks to their stage
        // copies. This does not validate all PointsStage entries or the
        // endoscalar bits; those checks follow with the endoscaling contract
        // enforcement.
        let (dr, stages) = common::load_all(dr, &witness)?;

        let allocator = &mut Standard::new();
        let mut unified = unified::OutputBuilder::new(witness.map(|w| w.instance));

        // The lifted challenges a parent opens this step at.
        let pairs = &stages.challenges.pairs;
        unified
            .x
            .receive(dr, allocator)?
            .enforce_equal(dr, &pairs[stages::challenges::X].lift)?;
        unified
            .y
            .receive(dr, allocator)?
            .enforce_equal(dr, &pairs[stages::challenges::Y].lift)?;
        unified
            .u
            .receive(dr, allocator)?
            .enforce_equal(dr, &pairs[stages::challenges::U].lift)?;

        // The commitments a parent endoscales, in `unified` order.
        let last_interstitial = stages
            .points
            .interstitials
            .last()
            .expect("NUM_ENDOSCALING_POINTS guarantees >= 1 interstitial");
        let held = [
            &stages.preamble.native_preamble,
            &stages.inner_error.native_inner_error,
            &stages.outer_error.native_outer_error,
            &stages.query.native_query,
            &stages.eval.native_eval,
            &stages.ab.a,
            &stages.ab.b,
            &stages.query.registry_xy,
            last_interstitial,
            &stages.eval.native_points_inputs,
        ];
        let exported = unified.exported.receive(dr, allocator)?;
        for (instance, stage) in exported.iter().zip(held) {
            instance.enforce_equal(dr, stage)?;
        }

        let (output, instance) = unified.finish(dr, allocator)?;
        Ok(WithAux::new(output, instance))
    }
}
