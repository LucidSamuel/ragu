# Merkle Path Verification

Merkle trees authenticate set membership by reducing a global root
commitment to a short sequence of sibling hashes along a path from a leaf
to the root. Verifying membership inside an arithmetic circuit follows the
same structure: at each level, the verifier conditionally reorders the
current node and its sibling, hashes them together, and repeats until it
reaches the root.

The [`merkle`][merkle-mod] module provides this verification as a pair of
functions, [`compute_root`] and [`enforce_inclusion`] operating over a
const-generic [`MerklePath`].

## [`MerklePath`]

A [`MerklePath`] holds `DEPTH` pairs of `(sibling, direction_bit)`,
ordered from the leaf level upward. The depth is a const generic, so the
number of wires is type-determined, satisfying
[fungibility](../gadgets/index.md#fungibility). Callers construct a path
from pre-allocated [`Element`]s and [`Boolean`]s:

```rust
let path = MerklePath::new([
    (sib0, dir0),
    (sib1, dir1),
    (sib2, dir2),
]);
```

Each direction bit describes which side of the hash the current node
occupies. A value of `false` places the current node on the left; `true`
places it on the right.

## [`compute_root`] and [`enforce_inclusion`]

[`compute_root`] hashes a leaf up a [`MerklePath`] and returns the
computed root as an [`Element`]. At each level it calls
[`Boolean::conditional_swap`] to reorder the current node and sibling,
absorbs both into a fresh Poseidon sponge, and squeezes the result:

```rust
let root = compute_root(dr, params, &leaf, &path)?;
```

[`enforce_inclusion`] does the same, then constrains the computed root to
equal an expected value:

```rust
enforce_inclusion(dr, params, &leaf, &path, &expected_root)?;
```

Both functions are generic over [`PoseidonPermutation`], so the hash
parameters are not fixed by the module.

## [`Boolean::conditional_swap`] {#conditional-swap}

Merkle path verification needs to reorder two elements based on a
direction bit. Two separate [`conditional_select`] calls would cost two
multiplication gates. [`Boolean::conditional_swap`] achieves the same
result with a single gate: it computes the difference of the two inputs
(free), multiplies by the bit (one gate), and derives both outputs from
the product (free).

## Cost

Each level of the path contributes one [`conditional_swap`] gate and one
Poseidon permutation, so a depth `DEPTH` verification costs

$$\text{DEPTH} \times (1 + \text{permutation gates})$$

Allocation of the leaf, siblings, and direction bits is the caller's
responsibility and is not included in this count.

[merkle-mod]: ragu_primitives::merkle
[`MerklePath`]: ragu_primitives::merkle::MerklePath
[`compute_root`]: ragu_primitives::merkle::compute_root
[`enforce_inclusion`]: ragu_primitives::merkle::enforce_inclusion
[`Boolean::conditional_swap`]: ragu_primitives::Boolean::conditional_swap
[`conditional_select`]: ragu_primitives::Boolean::conditional_select
[`Element`]: ragu_primitives::Element
[`Boolean`]: ragu_primitives::Boolean
[`PoseidonPermutation`]: ragu_arithmetic::PoseidonPermutation
