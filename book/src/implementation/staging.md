# Staging

The simplest circuits in Ragu commit to a single trace polynomial
$r(X)$ that encodes the entire witness. This works well for
self-contained computations, but breaks down when the prover needs
to interact with partial commitments during synthesis. Two
situations demand something more:

1. **In-circuit challenges.** The prover commits to a portion of the
   witness, hashes that commitment inside the circuit to obtain a
   Fiat-Shamir challenge, and uses the challenge in later
   computation. Partial traces are Pedersen vector commitments over
   potentially hundreds of wires, so hashing them is far cheaper
   than hashing the wires individually.
2. **Shared witness data.** Multiple circuits must operate over the
   same information. Communicating it through public inputs is
   expensive; sharing a pre-committed stage polynomial across
   circuits avoids that cost entirely.

The staging module in `ragu_circuits` implements this decomposition.
It splits $r(X)$ into independently committable **stage
polynomials** $a(X), b(X), \ldots$ plus a **final trace** $r'(X)$,
so that

$$
r(X) = r'(X) + a(X) + b(X) + \cdots
$$

The prover commits to each stage polynomial separately, then
completes the final trace using information derived from those
commitments.

## The `Stage` Trait {#stage-trait}

A stage is a partial trace component defined by implementing the
[`Stage`] trait:

```rust,ignore
pub trait Stage<F: Field, R: Rank> {
    type Parent: Stage<F, R>;
    type Witness<'source>: Send;
    type OutputKind: GadgetKind<F>;

    fn values() -> usize;

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, Self::Witness<'source>>,
    ) -> Result<Bound<'dr, D, Self::OutputKind>>
    where
        Self: 'dr;

    fn skip_multiplications() -> usize {
        Self::Parent::skip_multiplications()
            + Self::Parent::num_multiplications()
    }
}
```

The trait's associated types and methods define the stage's
interface:

- **`Parent`** links stages into a chain. The root stage uses `()`
  as its parent; each subsequent stage names the previous one.
  This linked-list structure lets the trait system compute wire
  offsets at compile time.
- **`values()`** returns the number of wires this stage allocates.
  The staging infrastructure derives the multiplication gate count
  as `values().div_ceil(2)`.
- **`witness()`** computes the stage's gadget from private data.
  The return type `Bound<'dr, D, Self::OutputKind>` is a
  driver-bound gadget that later stages can consume.
- **`OutputKind`** describes the prover-internal output carried
  between stages. This is distinct from
  [`MultiStageCircuit::Output`], which is the verifier-visible
  instance encoded into $k(Y)$.
- **`skip_multiplications()`** computes how many multiplication
  gates precede this stage in the trace. The default
  implementation recurses through the parent chain:
  `Parent::skip + Parent::num`.

The trivial `()` implementation anchors the chain with zero values
and zero skip.

## Wire Layout {#wire-layout}

Stages tile non-overlapping regions of the trace. Each stage
occupies a contiguous block of multiplication gates:

```text
r(X) = [ ONE | stage A wires | stage B wires | final r'(X) ]
         ^     skip=0,num=50   skip=50,num=2   skip=52
         |
         always skipped by stages (no ONE constraint)
```

The `ONE` gate at position 0 is skipped by all stage polynomials
because they carry no constant-wire constraint. After the `ONE`
gate, each stage's wires begin at `skip_multiplications()` and span
`num_multiplications()` gates. The final trace occupies all
remaining positions after the last explicit stage.

The staging infrastructure produces each stage's structured
polynomial by running the witness through an extractor emulator
and zero-padding all positions outside the stage's region; see
[`StageExt`](#stage-ext) for the concrete API.

## `StageExt` Blanket Trait {#stage-ext}

Every `Stage` implementation automatically gains extension methods
through the [`StageExt`] blanket impl:

- **`num_multiplications()`** returns `values().div_ceil(2)`.
- **`rx()` / `rx_configured()`** produce the stage's structured
  polynomial. The extractor emulator runs the witness, collects
  wire values, and places them at the correct offset with zeros
  elsewhere.
- **`mask()` / `final_mask()`** produce [`StageMask`] circuit
  objects for well-formedness checking (see
  [below](#stage-mask)).
- **`generator_index_for_a(i)`** returns the Pedersen generator
  index for the $i$-th A coefficient of this stage. The formula
  is $2n + 1 + \mathtt{skip} + i$, where $n$ is the rank
  parameter. This mapping enables challenge smuggling (see
  [below](#challenge-smuggling)).

## `StageBuilder` {#stage-builder}

The [`StageBuilder`] orchestrates multi-stage witness computation
using a two-phase typestate protocol.

### Phase 1: Wire Reservation

Call [`add_stage`] (or [`configure_stage`] for non-`Default` stages)
for each stage in parent-to-child order. Each call allocates wire
positions through the driver via a counter emulator, returns a
[`StageGuard`] holding the pre-allocated wires, and advances the
builder's type parameter:

```rust,ignore
let (preamble, builder) =
    builder.add_stage::<PreambleStage>()?;
let (query, builder) =
    builder.add_stage::<QueryStage>()?;
let (eval, builder) =
    builder.add_stage::<EvalStage>()?;
```

The type parameters `Current` and `Target` enforce compile-time
stage ordering: `add_stage::<Next>()` requires
`Next: Stage<Parent = Current>`, so skipping or reordering stages
is a type error.

[`skip_stage`] reserves wire positions without returning a guard,
for cases where the wire layout must match but the stage's output
is not needed.

### Phase 2: Witness Computation

When `Current == Target` (all stages have been added), `finish()`
becomes available and returns the underlying `&mut D` driver. The
caller then consumes each guard and completes the final trace:

```rust,ignore
let dr = builder.finish();

let preamble = preamble.enforced(dr, preamble_witness)?;
let query = query.unenforced(dr, query_witness)?;
let eval = eval.unenforced(dr, eval_witness)?;

// Remaining code computes r'(X) using stage outputs
```

This two-phase design ensures all provers agree on wire layout
before any witness values are computed.

## `StageGuard` {#stage-guard}

A [`StageGuard`] holds pre-allocated wires for a single stage.
It is marked `#[must_use]`, so dropping it without consumption
triggers a compiler warning. Two consuming methods are available:

- **`enforced(dr, witness)`** runs the stage's witness method on a
  [wireless emulator](drivers/emulator.md), substitutes
  pre-allocated wires via [`StageWireInjector`] (a [`FromDriver`]
  implementation), then calls `enforce_consistent()` — a method
  on the [`Consistent`] trait — to validate internal invariants
  such as curve equations.
- **`unenforced(dr, witness)`** performs the same wire injection
  but skips consistency enforcement.

```admonish info
[`StageWireInjector`] is a concrete [`FromDriver`] that replaces
wireless emulator wires with pre-allocated ones. Each
`convert_wire` call yields the next pre-allocated wire, maintaining
a one-to-one correspondence with the gadget's wire traversal
order.
```

The choice between `enforced` and `unenforced` depends on what the
stage contains. Stages with structured data types (Points, Booleans)
that carry internal invariants use `enforced`; stages that only
allocate raw field elements use `unenforced`.

## `StageMask` {#stage-mask}

A [`StageMask`] is a [`CircuitObject`] that generates the wiring
polynomial $s(X, Y)$ for well-formedness checking. Unlike normal
circuit objects, a `StageMask` has no `ONE` constraint: `sxy()`
returns zero when $x = 0$ or $y = 0$.

Two constructors cover the two cases:

- **`StageMask::new(skip, num)`** for intermediate stages. Wires
  outside the `skip..(skip + num)` range are constrained to zero.
- **`StageMask::new_final(skip)`** for the final trace. Takes all
  remaining multiplication gates after `skip`, so `num` is
  computed as `n - skip - 1`.

The constraint formula for a `StageMask` with rank parameter $n$ is:

- **Multiplication constraints:** $n$ (one per gate, including
  those constrained to zero)
- **Linear constraints:** $3(n - \text{num} - 1) + 2$ (three
  `enforce_zero` calls per unused gate, plus the `ONE`-wire
  constraint and the registry-key constraint)

To verify well-formedness, perform a revdot check between the
stage polynomial and the mask's wiring polynomial:

```rust,ignore
let a = MyStage::rx(witness)?;
let mask = MyStage::mask()?;
let sy = mask.sy(y, &registry_key, &[]);
assert_eq!(a.revdot(&sy), Fp::ZERO);
```

Stages that share the same mask can be combined with a random
challenge $z$ into a single revdot claim:
$\langle\!\langle \mathbf{a} + z\mathbf{b}, \mathbf{s}
\rangle\!\rangle = 0$. This batching works because
well-formedness checks are purely linear with no public inputs:
if both checks hold individually then the combined check holds
for all $z$, and a random $z$ detects a violation with
overwhelming probability.

## `MultiStageCircuit` {#multi-stage-circuit}

The [`MultiStageCircuit`] trait mirrors [`Circuit`] but replaces
the driver with a [`StageBuilder`]:

```rust,ignore
pub trait MultiStageCircuit<F: Field, R: Rank>: Sized + Send + Sync {
    type Last: Stage<F, R>;
    type Instance<'source>: Send;
    type Witness<'source>: Send;
    type Output: Write<F>;
    type Aux<'source>: Send;

    fn instance(...) -> Result<Bound<'dr, D, Self::Output>>;

    fn witness(
        &self,
        dr: StageBuilder<'a, 'dr, D, R, (), Self::Last>,
        witness: DriverValue<D, Self::Witness<'source>>,
    ) -> Result<(Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'source>>)>;
}
```

The key associated types:

- **`Last`** names the final stage in the parent chain. The builder
  starts at `()` and must reach `Last` before `finish()` unlocks.
- **`Output`** implements `Write<F>` and is the verifier-visible
  instance encoded into $k(Y)$. This is distinct from
  `Stage::OutputKind`, which carries prover-internal data.

The [`MultiStage`] adaptor wraps any `MultiStageCircuit` into a
[`Circuit`] implementation. It creates a fresh `StageBuilder`
inside its `witness` method and delegates to the inner circuit.
The adaptor also exposes `final_mask()` as a convenience proxy for
`Last::final_mask()`.

```admonish info
`MultiStageCircuit::Output` is serialized into the public input
polynomial $k(Y)$ and checked by the verifier.
`Stage::OutputKind` is prover-internal: it carries data between
stages but never appears in $k(Y)$.
```

## Challenge Smuggling {#challenge-smuggling}

The primary motivation for staging in practice is **challenge
smuggling**: deriving Fiat-Shamir challenges from partial-trace
commitments inside the circuit.

The pattern works as follows:

1. The prover allocates values into a stage polynomial $a(X)$.
2. The prover commits to $a(X)$ using Pedersen generators.
3. Inside the circuit, the prover hashes this commitment (a single
   curve point) to obtain a challenge.
4. The challenge drives later computation in the final trace.

[`StageExt::generator_index_for_a(i)`] maps the $i$-th wire of a
stage to its Pedersen generator index using the formula
$2n + 1 + \mathtt{skip} + i$. The circuit reconstructs the
commitment from
the stage's wire values and the corresponding generators; it
avoids a full multi-scalar multiplication by exploiting the
known structure of the Pedersen commitment.

For the protocol-level motivation, see the
[staging extensions](../protocol/extensions/staging.md) page
(item 1: partial traces as collision-resistant hashes).

## Summary {#summary}

The staging module decomposes a circuit's trace into independently
committable polynomials, enabling in-circuit challenge derivation
and cross-circuit witness sharing. The key components are:

- [`Stage`] defines a partial trace with parent-chain offsets
- [`StageBuilder`] two-phase typestate builder for wire
  reservation and witness computation
- [`StageGuard`] holds pre-allocated wires, consumed via
  `enforced()` or `unenforced()`
- [`StageMask`] circuit object for well-formedness revdot checks
- [`MultiStageCircuit`] / [`MultiStage`] trait and adaptor for
  staged circuits

For further reading:

- Protocol design:
  [Staging extensions](../protocol/extensions/staging.md)
- Polynomial management:
  [Polynomials](polynomials.md)
- Wire injection:
  [`FromDriver`] and [`StageWireInjector`]

[`Stage`]: ragu_circuits::staging::Stage
[`StageExt`]: ragu_circuits::staging::StageExt
[`StageBuilder`]: ragu_circuits::staging::StageBuilder
[`StageGuard`]: ragu_circuits::staging::StageGuard
[`StageWireInjector`]: ragu_circuits::staging::builder::StageWireInjector
[`StageMask`]: ragu_circuits::staging::mask::StageMask
[`MultiStageCircuit`]: ragu_circuits::staging::MultiStageCircuit
[`MultiStage`]: ragu_circuits::staging::MultiStage
[`StageExt::rx()`]: ragu_circuits::staging::StageExt::rx
[`StageExt::generator_index_for_a(i)`]: ragu_circuits::staging::StageExt::generator_index_for_a
[`CircuitObject`]: ragu_circuits::CircuitObject
[`Circuit`]: ragu_circuits::Circuit
[`Consistent`]: ragu_core::gadgets::Consistent
[`FromDriver`]: ragu_core::drivers::FromDriver
[`add_stage`]: ragu_circuits::staging::StageBuilder::add_stage
[`configure_stage`]: ragu_circuits::staging::StageBuilder::configure_stage
[`skip_stage`]: ragu_circuits::staging::StageBuilder::skip_stage
