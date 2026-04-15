# Troubleshooting

This page collects the errors and pitfalls that circuit developers
encounter most often, along with their causes and fixes. It is
organized by when you hit the problem: compile time, synthesis
(runtime), or registration.

## Compile-Time Errors {#compile-time}

### `Empty::take()` Panic {#empty-take}

```text
error[E0080]: evaluation of `<Empty<...> as Maybe<...>>::take`
              failed
  --> ragu_core/src/maybe/empty.rs
   |  panic!("Empty::take() called; ...")
```

**Cause**: You called `.take()` on a `DriverValue` inside a routine
or circuit body that gets synthesized with an `Empty`-typed driver.
`Empty` drivers never have witness data — calling `.take()` is a
compile-time trap that fires during monomorphization.

**Fix**: Only call `.take()` inside closures guarded by the `Maybe`
system (e.g., the witness closure passed to `mul()` or
`Allocator::alloc`). Outside those closures, use `.snag()` or
`.as_ref()` instead.

See the [DriverValue quick reference](#drivervalue-reference) below
for when to use each method.

### `Kind!` Type Mismatches {#kind-mismatch}

```text
error[E0308]: mismatched types
  expected: Bound<'dr, D, <LeafNode as Header<F>>::Output>
     found: Element<'dr, D>
```

**Cause**: `Header::encode` must return
`Result<Bound<'dr, D, Self::Output>>`, which wraps the gadget in a
`Bound`. Returning a bare `Element` won't match.

**Fix**: `Element::alloc` already returns `Result<Bound<...>>` when
the `Output` type is `Kind![F; Element<'_, _>]`. If you're building
a custom gadget, wrap it with `Bound::from(gadget)` or use
`Encoded::from_gadget()`.

### Allocator Trait Bound Errors {#allocator-bound}

```text
error[E0277]: the trait bound `(): Allocator<'_, D>`
              is not satisfied
```

**Cause**: `Element::alloc` requires an `&mut A` where
`A: Allocator`. If you pass a value instead of a mutable reference,
or forget the allocator parameter entirely, the compiler cannot
resolve the trait.

**Fix**: Pass `&mut ()` for the unit allocator or
`&mut SimpleAllocator::new()` for paired allocation. See the
[Allocation](gadgets/allocation.md) page.

## Synthesis Errors {#synthesis}

These errors occur at runtime during circuit synthesis. They are
variants of [`Error`] defined in `ragu_core`.

### `GateBoundExceeded` {#gate-bound}

```text
exceeded the maximum number of gates (32)
```

**Cause**: The circuit uses more multiplication gates than the
[`Rank`] allows. Each `mul()`, `gate()`, and allocation call
consumes one gate (though [`SimpleAllocator`] pairs two allocations
into one gate).

**Fix**: Either reduce gate count or use a larger rank. Use the
[Simulator](drivers/simulator.md) to measure:

```rust,ignore
let sim = Simulator::simulate(witness, |dr, w| {
    // your circuit code
    Ok(())
})?;
println!("gates: {}", sim.num_gates());
```

| Rank | Max gates |
|------|-----------|
| `R<7>` | 32 |
| `R<13>` | 2,048 |

### `ConstraintBoundExceeded` {#constraint-bound}

```text
exceeded the maximum number of constraints (128)
```

**Cause**: Too many `enforce_zero()` calls for the rank. Linear
constraints come from equality checks, boolean constraints, and
routine internals.

**Fix**: Same approach as `GateBoundExceeded` — measure with the
Simulator using `num_constraints()`, then choose an appropriate
rank.

### `InvalidWitness` {#invalid-witness}

```text
invalid witness: gate check failed
invalid witness: constraint failed
invalid witness: division by zero
```

**Cause**: The witness values do not satisfy the circuit's
constraints. Common triggers:

- **"gate check failed"**: The closure passed to `mul()` produced
  values where $a \cdot b \neq c$.
- **"constraint failed"**: An `enforce_zero()` linear combination
  evaluated to a nonzero value.
- **"division by zero"**: `Element::invert()` or
  `Element::div_nonzero()` received a zero denominator.

**Fix**: Check your witness computation logic. The Simulator
pinpoints the failing operation — the error propagates from the
exact gate or constraint that failed.

### `CircuitBoundExceeded` {#circuit-bound}

```text
exceeded the maximum number of circuits (256)
```

**Cause**: Too many circuits registered in a PCD context. Each step
and its internal circuits contribute to this count.

**Fix**: This is rare in application code. If you hit it, you may
need to consolidate steps or use a larger rank.

### `DegreeBoundExceeded` {#degree-bound}

```text
exceeded the maximum degree of a polynomial (64)
```

**Cause**: A polynomial exceeded its degree limit during synthesis.
Typically an internal error rather than something circuit code
triggers directly.

### `VectorLengthMismatch` {#vector-length}

```text
vector does not have the expected length: (expected 10, actual 5)
```

**Cause**: A `FixedVec` was constructed with the wrong number of
elements. The static length guarantee was violated at runtime.

**Fix**: Ensure the vector you pass matches the expected length
declared in the gadget's type.

### `MalformedEncoding` {#malformed-encoding}

```text
malformed encoding: stream ended
```

**Cause**: Proof deserialization failed. The byte stream was
truncated or corrupted.

### `Initialization` {#initialization}

```text
initialization failed: registry registration failed
initialization failed: two different Header implementations
    using the same suffix
```

**Cause**: Application setup failed. The most common trigger is
duplicate header suffixes — see [Registration
Errors](#registration) below.

## Registration Errors {#registration}

### Duplicate Header Suffix {#duplicate-suffix}

```text
initialization failed: two different Header implementations
    using the same suffix
```

**Cause**: Two distinct `Header` types were registered with the
same `Suffix` value. Each header must have a unique suffix.

**Fix**: Check your `const SUFFIX: Suffix = Suffix::new(N)` values
across all header types. Each must be unique within an application.

```rust,ignore
struct LeafNode;
impl<F: Field> Header<F> for LeafNode {
    const SUFFIX: Suffix = Suffix::new(0);  // OK
    // ...
}

struct InternalNode;
impl<F: Field> Header<F> for InternalNode {
    const SUFFIX: Suffix = Suffix::new(1);  // OK — different
    // ...
}
```

## `DriverValue` Quick Reference {#drivervalue-reference}

The `DriverValue<D, T>` type (alias for `Maybe<D::MaybeKind, T>`)
carries witness data through circuits. Three methods extract the
inner value, each appropriate in different contexts:

| Method | Returns | Panics on `Empty`? | Use when |
|--------|---------|-------------------|----------|
| `.take()` | `T` (owned) | Compile-time trap | Inside `mul()`/`alloc()` closures only |
| `.snag()` | `&T` | Compile-time trap | Inside `mul()`/`alloc()` closures when you need a reference |
| `.as_ref()` | `DriverValue<D, &T>` | Never | Everywhere else — preserves the `Maybe` wrapper |

**Rule of thumb**: use `.as_ref()` by default. Only reach for
`.take()` or `.snag()` inside the witness-producing closures where
the driver guarantees the value is available.

```rust,ignore
// Inside a mul() closure — .snag() is safe here
let (a, b, c) = dr.mul(|| {
    Ok((
        Coeff::Arbitrary(*x.value().snag()),
        Coeff::Arbitrary(*y.value().snag()),
        Coeff::Arbitrary(*product.snag()),
    ))
})?;

// Outside closures — use .as_ref()
let x_ref = x.value().as_ref();
```

## Circuit Patterns: Common Mistakes {#circuit-patterns}

### Branching Without `Boolean` {#branching}

Arithmetic circuits have no `if/else`. A common mistake is trying
to conditionally execute different circuit paths:

```rust,ignore
// WRONG — both branches always execute and allocate gates
if *condition.value().snag() {
    a.mul(dr, &b)?;
} else {
    a.add(dr, &c);
}
```

Both branches are synthesized regardless of the runtime value. The
constraint system sees every gate from both paths.

**Fix**: Use [`Boolean::conditional_select`] to choose between two
already-computed values:

```rust,ignore
let result_a = a.mul(dr, &b)?;
let result_b = a.add(dr, &c);
let result = condition.conditional_select(dr, &result_b, &result_a)?;
```

This costs one extra gate (the select) but produces a single
well-defined output wire. For conditional equality enforcement,
use [`Boolean::conditional_enforce_equal`].

### Forgetting That `add()` Is Free {#add-is-free}

Linear operations (`add`, `sub`, `scale`, `negate`) create virtual
wires with **zero gate cost**. Only `mul()`, `gate()`, and
allocation consume gates. A common over-optimization is trying to
batch additions into multiplications.

```rust,ignore
// Unnecessary: this uses a gate
let sum = a.mul(dr, &Element::one())?;

// Free: no gate cost
let sum = a.add(dr, &b);
```

### Division by Potentially-Zero Elements {#div-zero}

`Element::div_nonzero` and `Element::invert` both return
`InvalidWitness("division by zero")` when the denominator is zero.
The constraint is: the prover witnesses a quotient such that
`quotient * denominator = numerator`. When the denominator is zero,
the quotient is unconstrained — the prover can put anything there.

**Fix**: If the denominator might be zero, check with
`Element::is_zero` first and handle the zero case explicitly.

## Poseidon Sponge Errors {#poseidon}

### Squeezing an Empty Sponge {#empty-sponge}

```text
initialization failed: cannot squeeze from empty sponge:
    no values absorbed
```

**Cause**: `sponge.squeeze()` was called before any
`sponge.absorb()`. The sponge has no data to permute.

**Fix**: Always absorb at least one value before squeezing:

```rust,ignore
let mut sponge = Sponge::new(dr, &poseidon_params);
sponge.absorb(dr, &value)?;  // required before squeeze
let hash = sponge.squeeze(dr)?;
```

### `SaveError::AlreadyInSqueezeMode` {#save-squeeze}

```text
sponge is already in squeeze mode
```

**Cause**: `sponge.save_state()` was called after the sponge had
already transitioned to squeeze mode. The save/resume mechanism
captures the post-permutation state, which only makes sense during
the absorb phase.

**Fix**: Call `save_state()` after absorbing but before squeezing:

```rust,ignore
sponge.absorb(dr, &value)?;
let state = sponge.save_state(dr)?;  // OK — still absorbing
// Later:
let mut sponge = Sponge::resume(state, &poseidon_params);
let hash = sponge.squeeze(dr)?;
```

### `SaveError::NothingAbsorbed` {#save-empty}

```text
no values have been absorbed
```

**Cause**: `save_state()` was called on a fresh sponge with nothing
absorbed. There is no meaningful state to save.

**Fix**: Absorb at least one value before saving.

### Absorbing After Resume Without Squeezing {#resume-absorb}

This is not an error — it silently produces a wrong hash.

When you resume a sponge, it enters squeeze mode. If you absorb
before squeezing, the sponge switches back to absorb mode,
discarding the squeeze-mode state. The resulting hash differs from
what you would get by absorbing continuously.

```rust,ignore
// WRONG — absorbing before squeezing after resume
let state = sponge.save_state(dr)?;
let mut sponge = Sponge::resume(state, &params);
sponge.absorb(dr, &extra_value)?;  // switches back to absorb
let hash = sponge.squeeze(dr)?;    // different from expected

// CORRECT — squeeze first, then start a new absorb cycle
let mut sponge = Sponge::resume(state, &params);
let challenge = sponge.squeeze(dr)?;
// Now you can absorb again for a new round
sponge.absorb(dr, &extra_value)?;
```

[`Error`]: ragu_core::Error
[`Rank`]: ragu_circuits::polynomials::Rank
[`SimpleAllocator`]: ragu_primitives::allocator::SimpleAllocator
[`Boolean::conditional_select`]: ragu_primitives::Boolean::conditional_select
[`Boolean::conditional_enforce_equal`]: ragu_primitives::Boolean::conditional_enforce_equal
