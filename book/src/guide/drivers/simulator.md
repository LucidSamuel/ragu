# Simulator

The [Concrete Drivers](concrete.md) page introduced the [`Simulator`] as a
driver that executes circuit code natively while enforcing constraints and
tracking metrics. This page covers its public API and shows how to use it
to measure constraint costs before committing to a [`Rank`].

## Why Measure

Every circuit operates within the budget set by its
[`Rank`](../configuration.md). If the final circuit is too large, later
synthesis stages return an error such as:

```text
Error::GateBoundExceeded { limit: 32 }
```

The [`Simulator`] helps you catch this early. It runs circuit code exactly
as the real synthesis drivers do, calling witness closures, enforcing gate
constraints, and checking linear constraints but reports metrics instead of
building a proof. You can then compare those counts against the rank limits
before running the prover.

The simulator itself does **not** raise rank-bound errors. It gives you the
numbers that let you detect the problem before later synthesis code turns it
into `GateBoundExceeded` or `ConstraintBoundExceeded`.

## Rank Limits

| Rank | Max gates | Coefficient vector size | Typical use |
|------|-----------|-------------------------|-------------|
| `R<7>` | 32 | $2^7 = 128$ | Unit tests |
| `R<13>` | 2,048 | $2^{13} = 8{,}192$ | Production |

Gates correspond to [`mul()`] and [`gate()`] calls. Constraints
correspond to explicit [`enforce_zero()`] calls. The simulator
reports both so you can compare different circuit designs before
committing to a rank.

## API

[`Simulator`] is provided by `ragu_primitives` and re-exported at crate
root.

### Construction

```rust,ignore
use ragu_primitives::Simulator;

// Standalone
let mut dr = Simulator::<F>::new();

// With witness binding (preferred)
let sim = Simulator::simulate(witness_value, |dr, witness| {
    // circuit code here
    Ok(())
})?;
```

[`Simulator::simulate`] creates a fresh simulator, wraps the witness in
`Always<W>`, runs the closure, and returns the simulator with its
accumulated metrics. This is the standard entry point for measurement.

### Metrics

After synthesis completes, two counters are available:

| Method | Counts | Driver operation |
|--------|--------|-----------------|
| [`num_gates()`] | Multiplication gates | [`mul()`] / [`gate()`] |
| [`num_constraints()`] | Linear constraints enforced | [`enforce_zero()`] |

```rust,ignore
let sim = Simulator::simulate((a, b), |dr, witness| {
    let (a, b) = witness.cast();
    let allocator = &mut SimpleAllocator::new();
    let x = Element::alloc(dr, allocator, a)?;  // 1 gate
    let y = Element::alloc(dr, allocator, b)?;  // reuses stash
    Ok(())
})?;

assert_eq!(sim.num_gates(), 1);  // two allocations share one gate
```

### Resetting

[`reset()`] zeroes all counters without discarding the driver state. This
isolates the cost of a specific operation from setup overhead:

```rust,ignore
let sim = Simulator::simulate((x, z), |dr, witness| {
    let (x, z) = witness.cast();
    let allocator = &mut SimpleAllocator::new();
    let x = Element::alloc(dr, allocator, x)?;
    let z = Element::alloc(dr, allocator, z)?;

    dr.reset();  // ignore allocation cost above

    dr.routine(evaluator.clone(), (x, z))?;

    assert_eq!(dr.num_gates(), 76);
    assert_eq!(dr.num_constraints(), 152);

    Ok(())
})?;
```

This pattern is common in Ragu's own test suite: allocate inputs, reset,
run the operation under test, then assert on the counts.

## Constraint Checking

The [`Simulator`] does not merely count, it verifies. Every gate checks
$a \cdot b = c$, and every [`enforce_zero()`] checks that the linear
combination evaluates to zero. A constraint violation returns
`Error::InvalidWitness` immediately, pinpointing the failing operation.

This makes the simulator useful for catching witness bugs: if a circuit
produces incorrect assignments, the simulator rejects them before proving
is attempted.

## Routines

The [`Simulator`] always executes [routines](../routines.md) fully, even
when a routine can predict its output. This contrasts with the
[`Emulator`], which skips execution when prediction suffices. The simulator
uses prediction only to obtain auxiliary data, then still calls
`execute` so the full routine body contributes to the metrics and all of
its constraints are enforced.

## Example

Suppose you are writing a step that hashes two field elements with
Poseidon, and you want to know whether it fits in `R<7>` (32 gates):

```rust,ignore
use ragu_primitives::{Simulator, allocator::SimpleAllocator};
use pasta_curves::Fp;

let sim = Simulator::simulate((Fp::from(1u64), Fp::from(2u64)), |dr, witness| {
    let (a, b) = witness.cast();
    let allocator = &mut SimpleAllocator::new();
    let a = Element::alloc(dr, allocator, a)?;
    let b = Element::alloc(dr, allocator, b)?;

    dr.reset();

    let mut sponge = Sponge::new(dr, &poseidon_params);
    sponge.absorb(dr, &a)?;
    sponge.absorb(dr, &b)?;
    let _hash = sponge.squeeze(dr)?;

    println!(
        "gates: {}, constraints: {}",
        dr.num_gates(),
        dr.num_constraints()
    );
    Ok(())
})?;
```

If `num_gates()` exceeds 32, the circuit does not fit in `R<7>` and you
need `R<13>` (2,048 gates) or a larger rank.

## Summary

The [`Simulator`] answers two questions before you run the prover:

1. **Does this circuit satisfy its own constraints?** If not, you have a
   witness bug.
2. **How many gates and constraints does it use?** If the count exceeds
   your rank's budget, choose a larger rank or optimize the circuit.

Use [`reset()`] to isolate individual operations, and structure tests
around exact metric assertions so regressions are caught immediately.

[`Simulator`]: ragu_primitives::Simulator
[`Simulator::simulate`]: ragu_primitives::Simulator::simulate
[`num_gates()`]: ragu_primitives::Simulator::num_gates
[`num_constraints()`]: ragu_primitives::Simulator::num_constraints
[`reset()`]: ragu_primitives::Simulator::reset
[`Rank`]: ragu_circuits::polynomials::Rank
[`mul()`]: ragu_core::drivers::Driver::mul
[`gate()`]: ragu_core::drivers::DriverTypes::gate
[`enforce_zero()`]: ragu_core::drivers::Driver::enforce_zero
[`Emulator`]: ragu_core::drivers::emulator::Emulator
