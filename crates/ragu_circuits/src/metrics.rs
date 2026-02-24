//! Circuit constraint analysis and metrics collection.
//!
//! This module provides constraint system analysis by simulating circuit
//! execution without computing actual values, counting the number of
//! multiplication and linear constraints a circuit requires.

use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::{
    Result,
    drivers::{Driver, DriverTypes, emulator::Emulator},
    gadgets::{Bound, GadgetKind},
    maybe::Empty,
    routines::Routine,
};
use ragu_primitives::GadgetExt;

use alloc::vec::Vec;
use core::marker::PhantomData;

use super::{Circuit, DriverScope};

/// Per-routine constraint counts collected during circuit synthesis.
///
/// Each record captures the number of multiplication and linear constraints
/// contributed by a single routine (in DFS order). These sizes are the raw
/// input to floor planning, which decides where each routine's constraints are
/// placed in the polynomial layout.
///
/// # Root Routine Recrod
///
/// **The first record (index 0) is not backed by a [`Routine`].**
/// It accumulates every constraint emitted directly at circuit scope: the gaps
/// between (and around) top-level routine calls. Each subsequent record
/// likewise only captures constraints *local* to its scope: constraints
/// delegated to a nested sub-routine are counted in the sub-routine's own
/// record, not in the parent's.
///
/// # Example
///
/// Consider a circuit with this synthesis order:
///
/// ```text
/// [gap0]  RoutineA  [gap1]  RoutineB{ [gapB0]  RoutineC  [gapB1] }  [gap2]
///
/// Root Routine: { gap0: 3*mul + 2*lc, gap1: 1*mul + 1*lc, gap2: 1*lc }
/// RoutineA: 2*mul + 3*lc
/// RoutineB: { gapB0: 1*mul + 2*lc, gapB1: 1*lc }
/// RoutineC: 1*mul + 2*lc
/// ```
///
/// The resulting records vector (DFS order) is:
///
/// | index | what        | mul | lc | note                                 |
/// |-------|-------------|-----|----|--------------------------------------|
/// | 0     | root        |  4  |  4 | gaps 0+1+2; **not** a `Routine`      |
/// | 1     | `RoutineA`  |  2  |  3 | A's own constraints                  |
/// | 2     | `RoutineB`  |  1  |  3 | gB0+gB1 only; `RoutineC` excluded    |
/// | 3     | `RoutineC`  |  1  |  2 | C's own constraints                  |
#[derive(Default)]
pub struct RoutineRecord {
    /// The number of multiplication constraints in this routine.
    pub num_multiplication_constraints: usize,

    /// The number of linear constraints in this routine, including constraints
    /// on wires of the input gadget and on wires allocated within the routine.
    pub num_linear_constraints: usize,
}

/// Performs full constraint system analysis, capturing basic details about a circuit's topology through simulation.
pub struct CircuitMetrics {
    /// The number of linear constraints, including those for instance enforcement.
    pub num_linear_constraints: usize,

    /// The number of multiplication constraints, including those used for allocations.
    pub num_multiplication_constraints: usize,

    /// The degree of the instance polynomial $k(Y)$.
    // TODO(ebfull): not sure if we'll need this later
    #[allow(dead_code)]
    pub degree_ky: usize,

    /// Per-routine constraint records in synthesis order.
    ///
    /// See [`RoutineRecord`] for the indexing convention, including the
    /// special root record (index 0), which is not a [`Routine`].
    pub routines: Vec<RoutineRecord>,
}

/// Per-routine state that is saved and restored by [`DriverScope`].
struct CounterScope {
    available_b: bool,
    current_record: usize,
}

struct Counter<F> {
    scope: CounterScope,
    num_linear_constraints: usize,
    num_multiplication_constraints: usize,
    records: Vec<RoutineRecord>,
    _marker: PhantomData<F>,
}

impl<F: Field> DriverScope<CounterScope> for Counter<F> {
    fn scope(&mut self) -> &mut CounterScope {
        &mut self.scope
    }
}

impl<F: Field> DriverTypes for Counter<F> {
    type MaybeKind = Empty;
    type ImplField = F;
    type ImplWire = ();
    type LCadd = ();
    type LCenforce = ();
}

impl<'dr, F: Field> Driver<'dr> for Counter<F> {
    type F = F;
    type Wire = ();
    const ONE: Self::Wire = ();

    fn alloc(&mut self, _: impl Fn() -> Result<Coeff<Self::F>>) -> Result<Self::Wire> {
        if self.scope.available_b {
            self.scope.available_b = false;
            Ok(())
        } else {
            self.scope.available_b = true;
            self.mul(|| unreachable!())?;

            Ok(())
        }
    }

    fn mul(
        &mut self,
        _: impl Fn() -> Result<(Coeff<F>, Coeff<F>, Coeff<F>)>,
    ) -> Result<(Self::Wire, Self::Wire, Self::Wire)> {
        self.num_multiplication_constraints += 1;
        self.records[self.scope.current_record].num_multiplication_constraints += 1;

        Ok(((), (), ()))
    }

    fn add(&mut self, _: impl Fn(Self::LCadd) -> Self::LCadd) -> Self::Wire {}

    fn enforce_zero(&mut self, _: impl Fn(Self::LCenforce) -> Self::LCenforce) -> Result<()> {
        self.num_linear_constraints += 1;
        self.records[self.scope.current_record].num_linear_constraints += 1;
        Ok(())
    }

    fn routine<Ro: Routine<Self::F> + 'dr>(
        &mut self,
        routine: Ro,
        input: Bound<'dr, Self, Ro::Input>,
    ) -> Result<Bound<'dr, Self, Ro::Output>> {
        self.records.push(RoutineRecord::default());
        let record = self.records.len() - 1;
        self.with_scope(
            CounterScope {
                available_b: false,
                current_record: record,
            },
            |this| {
                let mut dummy = Emulator::wireless();
                let dummy_input = Ro::Input::map_gadget(&input, &mut dummy)?;
                let aux = routine.predict(&mut dummy, &dummy_input)?.into_aux();
                let result = routine.execute(this, input, aux)?;

                // Verify internal consistency: current_record unchanged and
                // all paired allocations consumed.
                assert_eq!(
                    this.scope.current_record, record,
                    "current_record must remain stable during routine execution"
                );
                assert!(
                    !this.scope.available_b,
                    "all paired allocations must be consumed"
                );

                Ok(result)
            },
        )
    }
}

pub fn eval<F: Field, C: Circuit<F>>(circuit: &C) -> Result<CircuitMetrics> {
    let mut collector = Counter {
        scope: CounterScope {
            available_b: false,
            current_record: 0,
        },
        num_linear_constraints: 0,
        num_multiplication_constraints: 0,
        records: alloc::vec![RoutineRecord::default()],
        _marker: PhantomData,
    };
    let mut degree_ky = 0usize;

    // ONE gate
    collector.mul(|| Ok((Coeff::One, Coeff::One, Coeff::One)))?;

    // Registry key constraint
    collector.enforce_zero(|lc| lc)?;

    // Circuit synthesis
    let (io, _) = circuit.witness(&mut collector, Empty)?;
    io.write(&mut collector, &mut degree_ky)?;

    // Public output constraints
    for _ in 0..degree_ky {
        collector.enforce_zero(|lc| lc)?;
    }

    // ONE constraint
    collector.enforce_zero(|lc| lc)?;

    let recorded_multiplications: usize = collector
        .records
        .iter()
        .map(|r| r.num_multiplication_constraints)
        .sum();
    let recorded_linear_constraints: usize = collector
        .records
        .iter()
        .map(|r| r.num_linear_constraints)
        .sum();
    assert_eq!(
        recorded_multiplications,
        collector.num_multiplication_constraints
    );
    assert_eq!(
        recorded_linear_constraints,
        collector.num_linear_constraints
    );

    Ok(CircuitMetrics {
        num_linear_constraints: collector.num_linear_constraints,
        num_multiplication_constraints: collector.num_multiplication_constraints,
        degree_ky,
        routines: collector.records,
    })
}
