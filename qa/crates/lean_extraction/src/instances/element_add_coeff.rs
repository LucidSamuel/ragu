use ragu_arithmetic::Coeff;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct ElementAddCoeffInstance;

impl CircuitInstance for ElementAddCoeffInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_wires_x = dr.alloc_input_wires(1);
        let input_wires_y = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::zero());
        let x = WireDeserializer::new(input_wires_x).into_gadget(&element_template)?;
        let y = WireDeserializer::new(input_wires_y).into_gadget(&element_template)?;

        // Representative coefficient for extraction. Distinct from Scale's `5`
        // so the two gadgets are visually distinguishable in the autogen.
        let coeff = Coeff::Arbitrary(Fp::from(7));
        let result = x.add_coeff(dr, &y, coeff);

        WireCollector::collect_from(&result)
    }
}
