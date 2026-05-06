//! Merkle tree path verification gadget.
//!
//! Provides [`compute_root`] and [`enforce_inclusion`] for verifying Merkle
//! authentication paths inside arithmetic circuits. Callers allocate the leaf,
//! siblings, and direction bits; this module only performs the hash-chain
//! computation.
//!
//! The path depth `DEPTH` is a const generic, enforcing compile-time
//! fixed-depth synthesis as required by Ragu's
//! [fungibility invariant](ragu_core::gadgets).
//!
//! # Cost
//!
//! A depth-`DEPTH` verification performs `DEPTH` iterations, each consisting
//! of one [`conditional_swap`](crate::Boolean::conditional_swap) multiplication
//! (1 gate) and a sponge round whose cost depends on the selected
//! [`PoseidonPermutation`]. When `P::RATE >= 2`, each level absorbs both inputs
//! before the first squeeze-triggered permutation, so the total gate cost is
//! `DEPTH × (1 + permutation_gates)`.
//!
//! With the default Pasta Poseidon parameters, one permutation costs 288 gates,
//! giving **289 gates per level**.

use ragu_arithmetic::PoseidonPermutation;
use ragu_core::{
    Result,
    drivers::Driver,
    gadgets::Gadget,
};

use crate::{Boolean, Element, poseidon::Sponge};

/// A Merkle authentication path of compile-time depth `DEPTH`.
///
/// Each entry is a `(sibling, direction_bit)` pair, ordered from the leaf
/// level upward. The direction bit convention:
/// - `false` (0): current node is on the **left**, sibling is on the right.
/// - `true` (1): current node is on the **right**, sibling is on the left.
#[derive(Gadget)]
pub struct MerklePath<'dr, D: Driver<'dr>, const DEPTH: usize> {
    #[ragu(gadget)]
    entries: [(Element<'dr, D>, Boolean<'dr, D>); DEPTH],
}

impl<'dr, D: Driver<'dr>, const DEPTH: usize> MerklePath<'dr, D, DEPTH> {
    /// Creates a path from an array of `(sibling, direction)` pairs.
    pub fn new(entries: [(Element<'dr, D>, Boolean<'dr, D>); DEPTH]) -> Self {
        Self { entries }
    }

    /// Returns a reference to the path entries.
    pub fn entries(&self) -> &[(Element<'dr, D>, Boolean<'dr, D>); DEPTH] {
        &self.entries
    }
}

/// Computes the Merkle root by hashing a leaf up a [`MerklePath`].
///
/// At each level, the current node and sibling are conditionally swapped
/// according to the direction bit, then hashed with Poseidon to produce the
/// next level's node.
///
/// # Errors
///
/// Returns an error if any constraint operation fails (e.g., gate bound
/// exceeded).
pub fn compute_root<'dr, D, P, const DEPTH: usize>(
    dr: &mut D,
    params: &'dr P,
    leaf: &Element<'dr, D>,
    path: &MerklePath<'dr, D, DEPTH>,
) -> Result<Element<'dr, D>>
where
    D: Driver<'dr>,
    P: PoseidonPermutation<D::F>,
{
    let mut current = leaf.clone();

    for (sibling, direction) in path.entries() {
        let (left, right) = direction.conditional_swap(dr, &current, sibling)?;

        let mut sponge = Sponge::<'_, D, P>::new(dr, params);
        sponge.absorb(dr, &left)?;
        sponge.absorb(dr, &right)?;
        current = sponge.squeeze(dr)?;
    }

    Ok(current)
}

/// Enforces that a leaf is included in a Merkle tree with the given root.
///
/// This is equivalent to [`compute_root`] followed by an equality constraint
/// between the computed and expected roots.
///
/// # Errors
///
/// Returns an error if any constraint operation fails or if the computed root
/// does not match `expected_root` (i.e., the witness is inconsistent).
pub fn enforce_inclusion<'dr, D, P, const DEPTH: usize>(
    dr: &mut D,
    params: &'dr P,
    leaf: &Element<'dr, D>,
    path: &MerklePath<'dr, D, DEPTH>,
    expected_root: &Element<'dr, D>,
) -> Result<()>
where
    D: Driver<'dr>,
    P: PoseidonPermutation<D::F>,
{
    let computed = compute_root(dr, params, leaf, path)?;
    dr.enforce_equal(computed.wire(), expected_root.wire())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use ragu_arithmetic::Cycle;
    use ragu_core::maybe::Maybe;
    use ragu_pasta::{Fp, Pasta};

    use super::*;
    use crate::{Simulator, allocator::Standard};

    type Sim = Simulator<Fp>;
    type PoseidonParams = <Pasta as Cycle>::CircuitPoseidon;

    /// Compute a Poseidon hash of two field elements outside the circuit
    /// (using the simulator) for test oracle construction.
    fn hash_pair(params: &PoseidonParams, a: Fp, b: Fp) -> Fp {
        let mut dr = Sim::new();
        let allocator = &mut Standard::new();
        let a = Element::alloc(&mut dr, allocator, Sim::just(|| a)).unwrap();
        let b = Element::alloc(&mut dr, allocator, Sim::just(|| b)).unwrap();
        let mut sponge = Sponge::<'_, Sim, PoseidonParams>::new(&mut dr, params);
        sponge.absorb(&mut dr, &a).unwrap();
        sponge.absorb(&mut dr, &b).unwrap();
        let out = sponge.squeeze(&mut dr).unwrap();
        *out.value().take()
    }

    // ---------------------------------------------------------------
    // Positive tests (tier 1): verify correct inputs produce correct roots
    // ---------------------------------------------------------------

    #[test]
    fn compute_root_depth_1() -> Result<()> {
        let baked = Pasta::baked();
        let params = Pasta::circuit_poseidon(baked);

        let leaf = Fp::from(42u64);
        let sibling = Fp::from(99u64);
        let expected_root = hash_pair(params, leaf, sibling);

        Sim::simulate((leaf, sibling, false), |dr, witness| {
            let (leaf_val, sib_val, dir_val) = witness.cast();
            let allocator = &mut Standard::new();

            let leaf = Element::alloc(dr, allocator, leaf_val)?;
            let sibling = Element::alloc(dr, allocator, sib_val)?;
            let direction = Boolean::alloc(dr, allocator, dir_val)?;

            let path = MerklePath::new([(sibling, direction)]);
            let root = compute_root(dr, params, &leaf, &path)?;

            assert_eq!(*root.value().take(), expected_root);
            Ok(())
        })?;

        Ok(())
    }

    #[test]
    fn compute_root_depth_1_swapped() -> Result<()> {
        let baked = Pasta::baked();
        let params = Pasta::circuit_poseidon(baked);

        let leaf = Fp::from(42u64);
        let sibling = Fp::from(99u64);
        let expected_root = hash_pair(params, sibling, leaf);

        Sim::simulate((leaf, sibling, true), |dr, witness| {
            let (leaf_val, sib_val, dir_val) = witness.cast();
            let allocator = &mut Standard::new();

            let leaf = Element::alloc(dr, allocator, leaf_val)?;
            let sibling = Element::alloc(dr, allocator, sib_val)?;
            let direction = Boolean::alloc(dr, allocator, dir_val)?;

            let path = MerklePath::new([(sibling, direction)]);
            let root = compute_root(dr, params, &leaf, &path)?;

            assert_eq!(*root.value().take(), expected_root);
            Ok(())
        })?;

        Ok(())
    }

    #[test]
    fn compute_root_depth_3() -> Result<()> {
        let baked = Pasta::baked();
        let params = Pasta::circuit_poseidon(baked);

        let leaf = Fp::from(1u64);
        let sib0 = Fp::from(2u64);
        let sib1 = Fp::from(3u64);
        let sib2 = Fp::from(4u64);

        let h0 = hash_pair(params, leaf, sib0);
        let h1 = hash_pair(params, sib1, h0);
        let expected_root = hash_pair(params, h1, sib2);

        let witness = (leaf, sib0, sib1, sib2);
        Sim::simulate(witness, |dr, w| {
            let (leaf_val, s0, s1, s2) = w.cast();
            let allocator = &mut Standard::new();

            let leaf = Element::alloc(dr, allocator, leaf_val)?;
            let sibling0 = Element::alloc(dr, allocator, s0)?;
            let sibling1 = Element::alloc(dr, allocator, s1)?;
            let sibling2 = Element::alloc(dr, allocator, s2)?;

            let dir0 = Boolean::alloc(dr, allocator, Sim::just(|| false))?;
            let dir1 = Boolean::alloc(dr, allocator, Sim::just(|| true))?;
            let dir2 = Boolean::alloc(dr, allocator, Sim::just(|| false))?;

            let path = MerklePath::new([
                (sibling0, dir0),
                (sibling1, dir1),
                (sibling2, dir2),
            ]);
            let root = compute_root(dr, params, &leaf, &path)?;

            assert_eq!(*root.value().take(), expected_root);
            Ok(())
        })?;

        Ok(())
    }

    #[test]
    fn enforce_inclusion_valid() -> Result<()> {
        let baked = Pasta::baked();
        let params = Pasta::circuit_poseidon(baked);

        let leaf = Fp::from(7u64);
        let sibling = Fp::from(13u64);
        let expected_root = hash_pair(params, leaf, sibling);

        Sim::simulate((leaf, sibling, expected_root), |dr, witness| {
            let (leaf_val, sib_val, root_val) = witness.cast();
            let allocator = &mut Standard::new();

            let leaf = Element::alloc(dr, allocator, leaf_val)?;
            let sibling = Element::alloc(dr, allocator, sib_val)?;
            let direction = Boolean::alloc(dr, allocator, Sim::just(|| false))?;
            let root = Element::alloc(dr, allocator, root_val)?;

            let path = MerklePath::new([(sibling, direction)]);
            enforce_inclusion(dr, params, &leaf, &path, &root)?;
            Ok(())
        })?;

        Ok(())
    }

    #[test]
    fn gate_cost_per_level() -> Result<()> {
        let baked = Pasta::baked();
        let params = Pasta::circuit_poseidon(baked);

        let leaf = Fp::from(1u64);
        let sibling = Fp::from(2u64);

        let sim = Sim::simulate((leaf, sibling, false), |dr, witness| {
            let (leaf_val, sib_val, dir_val) = witness.cast();
            let allocator = &mut Standard::new();

            let leaf = Element::alloc(dr, allocator, leaf_val)?;
            let sibling = Element::alloc(dr, allocator, sib_val)?;
            let direction = Boolean::alloc(dr, allocator, dir_val)?;

            dr.reset();
            let path = MerklePath::new([(sibling, direction)]);
            compute_root(dr, params, &leaf, &path)?;
            Ok(())
        })?;

        // 1 gate (conditional_swap) + 288 gates (Poseidon permutation)
        assert_eq!(sim.num_gates(), 289);
        Ok(())
    }

    // ---------------------------------------------------------------
    // Negative tests (tier 2): verify invalid inputs cause constraint failure
    // ---------------------------------------------------------------

    /// Build a valid depth-2 proof and return the components.
    fn valid_depth_2(
        params: &PoseidonParams,
    ) -> (Fp, Fp, Fp, bool, bool, Fp) {
        let leaf = Fp::from(10u64);
        let sib0 = Fp::from(20u64);
        let sib1 = Fp::from(30u64);
        let dir0 = false;
        let dir1 = true;

        let h0 = hash_pair(params, leaf, sib0);
        let root = hash_pair(params, sib1, h0);

        (leaf, sib0, sib1, dir0, dir1, root)
    }

    /// Helper: run enforce_inclusion with depth-2 parameters and return
    /// whether it succeeds.
    fn try_inclusion(
        params: &PoseidonParams,
        leaf: Fp,
        sib0: Fp,
        sib1: Fp,
        dir0: bool,
        dir1: bool,
        root: Fp,
    ) -> bool {
        Sim::simulate((leaf, sib0, sib1, root), |dr, w| {
            let (leaf_val, s0, s1, root_val) = w.cast();
            let allocator = &mut Standard::new();

            let leaf = Element::alloc(dr, allocator, leaf_val)?;
            let sibling0 = Element::alloc(dr, allocator, s0)?;
            let sibling1 = Element::alloc(dr, allocator, s1)?;
            let root = Element::alloc(dr, allocator, root_val)?;

            let d0 = Boolean::alloc(dr, allocator, Sim::just(|| dir0))?;
            let d1 = Boolean::alloc(dr, allocator, Sim::just(|| dir1))?;

            let path = MerklePath::new([(sibling0, d0), (sibling1, d1)]);
            enforce_inclusion(dr, params, &leaf, &path, &root)?;
            Ok(())
        })
        .is_ok()
    }

    #[test]
    fn rejects_mutated_leaf() {
        let baked = Pasta::baked();
        let params = Pasta::circuit_poseidon(baked);
        let (leaf, sib0, sib1, dir0, dir1, root) = valid_depth_2(params);

        // Valid proof passes.
        assert!(try_inclusion(params, leaf, sib0, sib1, dir0, dir1, root));

        // Mutated leaf fails.
        let bad_leaf = leaf + Fp::ONE;
        assert!(!try_inclusion(params, bad_leaf, sib0, sib1, dir0, dir1, root));
    }

    #[test]
    fn rejects_corrupted_sibling() {
        let baked = Pasta::baked();
        let params = Pasta::circuit_poseidon(baked);
        let (leaf, sib0, sib1, dir0, dir1, root) = valid_depth_2(params);

        // Corrupt sibling at level 0.
        let bad_sib0 = sib0 + Fp::ONE;
        assert!(!try_inclusion(params, leaf, bad_sib0, sib1, dir0, dir1, root));

        // Corrupt sibling at level 1.
        let bad_sib1 = sib1 + Fp::ONE;
        assert!(!try_inclusion(params, leaf, sib0, bad_sib1, dir0, dir1, root));
    }

    #[test]
    fn rejects_flipped_direction_bit() {
        let baked = Pasta::baked();
        let params = Pasta::circuit_poseidon(baked);
        let (leaf, sib0, sib1, dir0, dir1, root) = valid_depth_2(params);

        // Flip direction bit at level 0.
        assert!(!try_inclusion(params, leaf, sib0, sib1, !dir0, dir1, root));

        // Flip direction bit at level 1.
        assert!(!try_inclusion(params, leaf, sib0, sib1, dir0, !dir1, root));
    }

    #[test]
    fn rejects_wrong_expected_root() {
        let baked = Pasta::baked();
        let params = Pasta::circuit_poseidon(baked);
        let (leaf, sib0, sib1, dir0, dir1, root) = valid_depth_2(params);

        let wrong_root = root + Fp::ONE;
        assert!(!try_inclusion(params, leaf, sib0, sib1, dir0, dir1, wrong_root));
    }
}
