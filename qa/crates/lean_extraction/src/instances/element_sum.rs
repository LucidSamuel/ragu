use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct ElementSumInstance;

impl CircuitInstance for ElementSumInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // Length 3: representative of the variadic `Element::sum`. For other
        // lengths, add analogous instances.
        let input_wires_0 = dr.alloc_input_wires(1);
        let input_wires_1 = dr.alloc_input_wires(1);
        let input_wires_2 = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::zero());
        let x0 = WireDeserializer::new(input_wires_0).into_gadget(&element_template)?;
        let x1 = WireDeserializer::new(input_wires_1).into_gadget(&element_template)?;
        let x2 = WireDeserializer::new(input_wires_2).into_gadget(&element_template)?;

        let result = Element::sum(dr, [&x0, &x1, &x2]);

        WireCollector::collect_from(&result)
    }
}
