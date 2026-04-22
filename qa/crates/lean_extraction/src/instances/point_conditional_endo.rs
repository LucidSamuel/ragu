use group::prime::PrimeCurveAffine;
use ragu_core::drivers::Driver;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::{Boolean, Point};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct PointConditionalEndoInstance;

impl CircuitInstance for PointConditionalEndoInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let cond_wires = dr.alloc_input_wires(1);
        let point_wires = dr.alloc_input_wires(2);

        let cond = Boolean::promote(
            cond_wires[0].clone(),
            ExtractionDriver::<Fp>::just(|| false),
        );

        let template = Point::constant(dr, EpAffine::generator())?;
        let input_point = WireDeserializer::new(point_wires).into_gadget(&template)?;

        // `conditional_endo` is composite: `self.x.scale(ζ)` (virtual),
        // `condition.conditional_select(self.x, endo_x)` (one mul gate + 2
        // enforce_equals), then reassembles into a Point with the selected x
        // and the original y. Emits 3 wires + 3 asserts.
        let result = input_point.conditional_endo(dr, &cond)?;

        WireCollector::collect_from(&result)
    }
}
