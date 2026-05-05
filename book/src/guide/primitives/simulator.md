# Simulator

The [`Simulator`] is a driver that fully executes circuit synthesis natively.
Every gate's $a \cdot b = c$ relation is checked, every [`enforce_zero()`]
call verifies that its linear combination evaluates to zero, and gate and
constraint counts are tracked along the way. A failed check returns
`Error::InvalidWitness` immediately, pinpointing the offending operation.

This makes the simulator the standard testing tool in Ragu, used both to
catch bugs and to produce realistic measurements you can compare against
your circuit's [`Rank`](../configuration.md) budget.

## Running and Measuring

[`Simulator::simulate`] is the standard entry point. It builds a fresh
simulator, wraps the witness in `Always<W>`, runs the closure, and returns
the simulator with its accumulated metrics. After it returns,
[`num_gates()`] and [`num_constraints()`] expose the counts:

```rust,ignore
let sim = Simulator::simulate((a, b), |dr, witness| {
    let (a, b) = witness.cast();
    let allocator = &mut Standard::new();
    let _x = Element::alloc(dr, allocator, a)?;  // 1 gate
    let _y = Element::alloc(dr, allocator, b)?;  // reuses stash
    Ok(())
})?;

assert_eq!(sim.num_gates(), 1);
```

[`reset()`] zeroes both counters in place, isolating the cost of a
sub-operation from setup overhead. The pattern — allocate inputs, reset,
run the operation under test, assert — appears throughout Ragu's own test
suite:

```rust,ignore
let sim = Simulator::simulate((x, z), |dr, witness| {
    let (x, z) = witness.cast();
    let allocator = &mut Standard::new();
    let x = Element::alloc(dr, allocator, x)?;
    let z = Element::alloc(dr, allocator, z)?;

    dr.reset();
    dr.routine(evaluator.clone(), (x, z))?;

    assert_eq!(dr.num_gates(), 76);
    assert_eq!(dr.num_constraints(), 152);
    Ok(())
})?;
```

## Example

To confirm that a chain of element multiplications fits inside `R<7>`
(32 gates) before committing to a rank:

```rust,ignore
use ragu_pasta::Fp;
use ragu_primitives::{Element, Simulator, allocator::Standard};

let sim = Simulator::simulate((Fp::from(2u64), Fp::from(3u64)), |dr, witness| {
    let (a, b) = witness.cast();
    let allocator = &mut Standard::new();
    let a = Element::alloc(dr, allocator, a)?;
    let b = Element::alloc(dr, allocator, b)?;

    dr.reset();

    let ab = a.mul(dr, &b)?;
    let _abb = ab.mul(dr, &b)?;
    Ok(())
})?;

assert!(sim.num_gates() < 1 << 7);
```

If `num_gates()` exceeds 32, the circuit doesn't fit in `R<7>`; pick a
larger rank or simplify the circuit.

[`Simulator`]: ragu_primitives::Simulator
[`Simulator::simulate`]: ragu_primitives::Simulator::simulate
[`num_gates()`]: ragu_primitives::Simulator::num_gates
[`num_constraints()`]: ragu_primitives::Simulator::num_constraints
[`reset()`]: ragu_primitives::Simulator::reset
[`Rank`]: ragu_circuits::polynomials::Rank
[`enforce_zero()`]: ragu_core::drivers::Driver::enforce_zero
