use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireDeserializer},
};

pub struct ElementEnforceNonzeroInstance;

impl CircuitInstance for ElementEnforceNonzeroInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // Extracts `Element::enforce_nonzero` as a standalone lemma circuit:
        // the discharge that every `NonzeroBank::scope` and every
        // `Element::divide` ultimately depends on. Lean reimpl spec:
        // `input ≠ 0`.
        let input_wires = dr.alloc_input_wires(1);
        let element_template = Element::constant(dr, Fp::zero());
        let elem = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        elem.enforce_nonzero(dr)?;

        Ok(Vec::new())
    }
}
