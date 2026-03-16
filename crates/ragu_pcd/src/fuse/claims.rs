//! Fuse-path claim source and commitment tracking.
//!
//! In the fuse pipeline the `A` polynomials need to carry their corresponding
//! commitments so that `_06_ab` can compute `a_commitment` via a small MSM
//! over known child-proof commitments instead of a full polynomial-degree MSM.
//!
//! Each polynomial entering the claims pipeline is tagged with a [`FuseAtom`]
//! key — a `(`[`Side`]`, `[`RxComponent`]`)` pair identifying which child
//! proof and component it came from. As polynomials are summed and folded,
//! the corresponding [`CommitmentDecomposition`] accumulates the linear
//! combination of those keys, so the final commitment can be resolved
//! directly from the child proofs.

use alloc::{borrow::Cow, vec::Vec};

use ff::PrimeField;
use ragu_arithmetic::Cycle;
use ragu_circuits::{
    polynomials::{Rank, structured},
    registry::CircuitIndex,
};
use ragu_core::Result;

use crate::{
    Proof,
    internal::{
        claims::{Builder, Source, sum_polynomials},
        fold_revdot::{CommitmentDecomposition, Decomposed},
        native::{InternalCircuitIndex, RxComponent, claims::Processor},
    },
};

/// A polynomial reference paired with a key that identifies the corresponding
/// commitment in the child proofs.
///
/// The fuse pipeline threads these through the claims builder so that each
/// `A` polynomial retains a link back to its commitment.
pub struct Atom<'rx, K, F: PrimeField, R: Rank> {
    pub key: K,
    pub poly: &'rx structured::Polynomial<F, R>,
}

// Manual Copy/Clone: derive(Copy) would incorrectly require F: Copy and R: Copy,
// but Atom only contains a reference and a K, both of which are always Copy.
impl<K: Copy, F: PrimeField, R: Rank> Clone for Atom<'_, K, F, R> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<K: Copy, F: PrimeField, R: Rank> Copy for Atom<'_, K, F, R> {}

/// Identifies which of the two child proofs a polynomial came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Side {
    Left,
    Right,
}

/// Key identifying a polynomial and its corresponding commitment within the
/// fuse pipeline: which child proof, and which component of that proof.
pub(crate) type FuseAtom = (Side, RxComponent);

/// The two child proofs being fused. Provides [`Atom`]-tagged rx values
/// for claim building, and resolves [`FuseAtom`] keys back to their
/// `(commitment, blind)` pairs for the MSM in `_06_ab`.
pub(crate) struct FuseProofSource<'rx, C: Cycle, R: Rank> {
    pub(crate) left: &'rx Proof<C, R>,
    pub(crate) right: &'rx Proof<C, R>,
}

impl<'rx, C: Cycle, R: Rank> FuseProofSource<'rx, C, R> {
    /// Look up the `(commitment, blind)` pair for a [`FuseAtom`] key in the
    /// corresponding child proof.
    #[allow(dead_code)] // used in next commit (_06_ab MSM optimization)
    pub(super) fn resolve_atom(
        &self,
        (side, component): FuseAtom,
    ) -> (C::HostCurve, C::CircuitField) {
        let proof = match side {
            Side::Left => self.left,
            Side::Right => self.right,
        };
        match component {
            RxComponent::AbA => (proof.ab.native.a_commitment, proof.ab.native.a_blind),
            RxComponent::AbB => (proof.ab.native.b_commitment, proof.ab.native.b_blind),
            RxComponent::Rx(idx) => proof.rx_commitment_blind(idx),
        }
    }
}

impl<'rx, C: Cycle, R: Rank> Source for FuseProofSource<'rx, C, R> {
    type RxComponent = RxComponent;
    type Rx = Atom<'rx, FuseAtom, C::CircuitField, R>;
    type AppCircuitId = CircuitIndex;

    fn rx(&self, component: RxComponent) -> impl Iterator<Item = Self::Rx> {
        [
            Atom {
                key: (Side::Left, component),
                poly: self.left.native_rx(component),
            },
            Atom {
                key: (Side::Right, component),
                poly: self.right.native_rx(component),
            },
        ]
        .into_iter()
    }

    fn app_circuits(&self) -> impl Iterator<Item = Self::AppCircuitId> {
        [
            self.left.application.circuit_id,
            self.right.application.circuit_id,
        ]
        .into_iter()
    }
}

/// Fuse-path [`Processor`] implementation.
///
/// Each method pairs the polynomial with a [`CommitmentDecomposition`] that
/// records how it decomposes as a linear combination of child-proof
/// polynomials (and therefore their commitments). The decomposition is
/// consumed in `_06_ab` to compute `a_commitment` via MSM.
impl<'m, 'rx, F: PrimeField, R: Rank> Processor<Atom<'rx, FuseAtom, F, R>, CircuitIndex>
    for Builder<'m, 'rx, Decomposed<'rx, FuseAtom, F, R>, F, R>
{
    fn raw_claim(&mut self, a: Atom<'rx, FuseAtom, F, R>, b: Atom<'rx, FuseAtom, F, R>) {
        self.a
            .push(Decomposed::single(Cow::Borrowed(a.poly), a.key));
        self.b.push(Cow::Borrowed(b.poly));
    }

    fn circuit(&mut self, circuit_id: CircuitIndex, rx: Atom<'rx, FuseAtom, F, R>) {
        self.circuit_impl(
            circuit_id,
            Decomposed::single(Cow::Borrowed(rx.poly), rx.key),
        );
    }

    fn internal_circuit(
        &mut self,
        id: InternalCircuitIndex,
        rxs: impl Iterator<Item = Atom<'rx, FuseAtom, F, R>>,
    ) {
        let atoms: Vec<_> = rxs.collect();
        // Plain sum: poly = sum_i rx_i, so each constituent has coefficient 1.
        let decomp = CommitmentDecomposition {
            terms: atoms.iter().map(|a| (a.key, F::ONE)).collect(),
        };
        let circuit_id = id.circuit_index();
        let poly = sum_polynomials(atoms.iter().map(|a| a.poly));
        self.circuit_impl(circuit_id, Decomposed::new(poly, decomp));
    }

    fn stage(
        &mut self,
        id: InternalCircuitIndex,
        rxs: impl Iterator<Item = Atom<'rx, FuseAtom, F, R>>,
    ) -> Result<()> {
        let atoms: Vec<_> = rxs.collect();
        let folded = self.fold_stage_polys(atoms.iter().map(|a| a.poly));

        // Compute z-power decomposition matching the Horner fold in
        // `fold_stage_polys`. The fold gives item i coefficient z^(n-1-i).
        let z = self.z;
        let mut terms = Vec::with_capacity(atoms.len());
        let mut z_pow = F::ONE;
        for atom in atoms.iter().rev() {
            terms.push((atom.key, z_pow));
            z_pow *= z;
        }
        terms.reverse();
        let decomp = CommitmentDecomposition { terms };

        self.stage_impl(id.circuit_index(), Decomposed::new(folded, decomp));
        Ok(())
    }
}
