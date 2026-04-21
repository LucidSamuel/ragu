use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::Boolean;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

pub struct BooleanAndInstance;

impl CircuitInstance for BooleanAndInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_a_wires = dr.alloc_input_wires(1);
        let input_b_wires = dr.alloc_input_wires(1);

        // `Boolean::promote` wraps input wires as already-allocated booleans.
        // Callers supply the boolean-ness guarantee via the Lean Spec's
        // `Assumptions`.
        let a = Boolean::promote(
            input_a_wires[0].clone(),
            ExtractionDriver::<Fp>::just(|| false),
        );
        let b = Boolean::promote(
            input_b_wires[0].clone(),
            ExtractionDriver::<Fp>::just(|| false),
        );

        // `Boolean::and` emits one mul gate plus two `enforce_equal`s (which
        // lower to `enforce_zero` in the trace).
        let result = a.and(dr, &b)?;

        WireCollector::collect_from(&result)
    }
}
