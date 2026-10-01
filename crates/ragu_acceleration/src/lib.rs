//! # `ragu_acceleration`
//!
//! Optimized implementations of Ragu's computational backend.
//!
//! Overrides fall back to the defaults of [`ragu_backend::Backend`] where a
//! method has none. The one override today is `msm`: the default plans Udon's
//! multiscalar multiplication over bounded stack scratch and runs it
//! serially, and the override plans it over scratch sized for the input and,
//! with the `multicore` feature, runs it on rayon's pool. Overrides of the
//! kernels that `ragu_pcd`'s verifier consults belong in [`verifier`], which
//! carries a stricter review and testing bar than prover-only overrides. An
//! override arrives with its differential test against the default it
//! replaces; `ragu_pcd`'s `backend_equivalence` tests hold
//! [`AcceleratedProver`] to the reference end to end.

#![no_std]
#![deny(missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]

extern crate alloc;
#[cfg(test)]
extern crate std;

use udon::curve::Affine;

pub mod verifier;

/// Ragu's accelerated computational backend, for proving and verification.
///
/// It computes exactly what [`ragu_backend::ReferenceBackend`] computes.
/// Selecting this backend in `ragu_pcd` also uses its verifier-consulted
/// kernels (see [`verifier`]) when verifying proofs. Select
/// [`AcceleratedProver`] to accelerate proving only.
#[derive(Clone, Copy, Debug, Default)]
pub struct AcceleratedBackend;

/// [`AcceleratedBackend`] for proving, with verification on the reference
/// kernels.
///
/// Computes exactly what [`AcceleratedBackend`] computes; the two differ only
/// in which kernels `ragu_pcd` consults when verifying. Selecting this type
/// keeps every acceptance decision on the canonical code path, at the cost of
/// the verifier-side speedups.
#[derive(Clone, Copy, Debug, Default)]
pub struct AcceleratedProver;

// `AcceleratedProver` must forward every override to `AcceleratedBackend`,
// one method per override, so the two impl blocks stay comparable and a new
// override cannot be selected for proving while silently missing here.
impl ragu_backend::Backend for AcceleratedBackend {
    fn msm<'a, C: Affine, A: IntoIterator<Item = &'a C::Scalar>, B: IntoIterator<Item = &'a C>>(
        coeffs: A,
        bases: B,
    ) -> C::Projective
    where
        B::IntoIter: Clone + Sync,
    {
        verifier::msm::msm(coeffs, bases)
    }
}

impl ragu_backend::Backend for AcceleratedProver {
    fn msm<'a, C: Affine, A: IntoIterator<Item = &'a C::Scalar>, B: IntoIterator<Item = &'a C>>(
        coeffs: A,
        bases: B,
    ) -> C::Projective
    where
        B::IntoIter: Clone + Sync,
    {
        <AcceleratedBackend as ragu_backend::Backend>::msm(coeffs, bases)
    }
}
