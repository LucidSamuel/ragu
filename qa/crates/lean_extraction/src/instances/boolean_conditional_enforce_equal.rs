use ff::Field;
use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::{Boolean, Element};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireDeserializer},
};

pub struct BooleanConditionalEnforceEqualInstance;

impl CircuitInstance for BooleanConditionalEnforceEqualInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let cond_wires = dr.alloc_input_wires(1);
        let a_wires = dr.alloc_input_wires(1);
        let b_wires = dr.alloc_input_wires(1);

        let cond = Boolean::promote(
            cond_wires[0].clone(),
            ExtractionDriver::<Fp>::just(|| false),
        );

        let element_template = Element::constant(dr, Fp::ZERO);
        let a = WireDeserializer::new(a_wires).into_gadget(&element_template)?;
        let b = WireDeserializer::new(b_wires).into_gadget(&element_template)?;

        // Emits a custom gate (3 wires) plus three `enforce_zero`s:
        // `cond_wire = cond_input`, `diff_wire = a - b`, `zero_wire = 0`.
        // With the gate constraint `cond_wire * diff_wire = zero_wire = 0`,
        // this enforces `cond * (a - b) = 0`.
        cond.conditional_enforce_equal(dr, &mut (), &a, &b)?;

        // No output wires; the gadget is an assertion, not a value.
        Ok(Vec::new())
    }
}
