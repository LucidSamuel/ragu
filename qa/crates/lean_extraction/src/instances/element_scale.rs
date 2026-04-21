use ragu_arithmetic::Coeff;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct ElementScaleInstance;

impl CircuitInstance for ElementScaleInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_wires = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::zero());
        let input = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        // Representative coefficient for extraction. `Coeff::Arbitrary` is the
        // most general variant; a fresh non-special value is used so that the
        // rendered hex literal doesn't collide with other gadgets' constants.
        let coeff = Coeff::Arbitrary(Fp::from(5));
        let scaled = input.scale(dr, coeff);

        WireCollector::collect_from(&scaled)
    }
}
