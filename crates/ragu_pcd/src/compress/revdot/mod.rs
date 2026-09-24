//! Reduction 1: from revdot claims to polynomial openings.
//!
//! The prover forms $t(X) = \sum_i \rho^i a_i(X) b_i(X)$ over the claims,
//! splits it as $t(X) = X^{n-1} p(1/X) + X^n q(X)$, so that $p(0) = \sum_i
//! \rho^i \operatorname{revdot}(a_i, b_i)$, and commits to $p$ and $q$. The
//! verifier squeezes $r$ and checks $\sum_i \rho^i a_i(r) b_i(r) = r^{n-1}
//! p(1/r) + r^n q(r)$ from the claimed openings, then hands every opening it
//! relied on to the batch: each committed polynomial at $r$ and $rz$, $p$ at
//! $1/r$ and at $0$, where it must equal $\sum_i \rho^i k_i(y)$, and $q$ at
//! $r$.
//!
//! Combining products rather than folding vectors leaves no cross terms, so
//! nothing but the two commitments and the claimed openings travels. Both
//! sides take the claims in the decider's order, the prover through
//! [`claims::Builder`](crate::internal::claims::Builder) and the verifier
//! through [`claims::native`](super::claims::native) and
//! [`claims::nested`](super::claims::nested).
//!
//! The transcript is assumed to have seen the commitments the claims are
//! over, and $y$ and $z$ to have been squeezed from it.

use alloc::{borrow::Cow, vec::Vec};

use ragu_arithmetic::{CurveAffine, ff::Field};
use ragu_circuits::polynomials::{Rank, sparse};
use ragu_core::{Error, Result};

use super::claims::Opened;
use crate::internal::{native, nested};

mod prover;
mod verifier;

pub(crate) use prover::{reduce_native, reduce_nested};
pub(crate) use verifier::{verify_native, verify_nested};

/// An opening claim: the polynomial at `poly` in an [`Openings`]' list takes
/// `value` at `point`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct OpeningClaim<F> {
    pub poly: usize,
    pub point: F,
    pub value: F,
}

/// The opening claims a reduction leaves for the batch, over the committed
/// polynomials they refer to: the components in order, then $p$, then $q$.
#[derive(Clone, Debug)]
pub(crate) struct Openings<C: CurveAffine> {
    pub commitments: Vec<C>,
    pub claims: Vec<OpeningClaim<C::Scalar>>,
}

/// The prover's messages of the reduction on one curve.
#[derive(Clone, Debug)]
pub(crate) struct Reduction<C: CurveAffine> {
    /// The commitment to $p$.
    pub p: C,
    /// The commitment to $q$.
    pub q: C,
    /// Each committed polynomial's claimed openings at $r$ and $rz$, in
    /// component order.
    pub openings: Vec<Opened<C::Scalar>>,
    /// The claimed $p(1/r)$.
    pub p_at_inverse_r: C::Scalar,
    /// The claimed $q(r)$.
    pub q_at_r: C::Scalar,
}

/// What the prover keeps to open $p$ and $q$ in the batch.
pub(crate) struct Witness<F> {
    /// The point the claims were opened at.
    pub r: F,
    /// $p$, with $n$ coefficients.
    pub p: Vec<F>,
    /// $q$, padded to $n$ coefficients.
    pub q: Vec<F>,
}

impl<F: Field> Witness<F> {
    /// The openings the verifier will require of `reduction` over
    /// `commitments`, the components' in order, as [`verify_native`] and
    /// [`verify_nested`] list them, with $p(0)$ read off $p$.
    pub(crate) fn openings<C: CurveAffine<ScalarExt = F>>(
        &self,
        commitments: Vec<C>,
        reduction: &Reduction<C>,
        z: F,
    ) -> Result<Openings<C>> {
        let inverse_r = invert(self.r)?;
        Ok(openings(
            commitments,
            reduction,
            self.r,
            z,
            inverse_r,
            self.p[0],
        ))
    }

    /// The polynomials behind an [`Openings`]' commitments, in its order:
    /// `committed` in component order, then $p$, then $q$.
    pub(crate) fn polys<'a, R: Rank>(
        &'a self,
        committed: impl IntoIterator<Item = &'a sparse::Polynomial<F, R>>,
    ) -> Vec<Cow<'a, sparse::Polynomial<F, R>>> {
        committed
            .into_iter()
            .map(Cow::Borrowed)
            .chain([
                Cow::Owned(sparse::Polynomial::from_coeffs(self.p.clone())),
                Cow::Owned(sparse::Polynomial::from_coeffs(self.q.clone())),
            ])
            .collect()
    }
}

/// The native components in the order their openings are listed.
pub(crate) fn native_components() -> impl Iterator<Item = native::RxComponent> {
    [native::RxComponent::AbA, native::RxComponent::AbB]
        .into_iter()
        .chain(
            native::RxIndex::ALL
                .into_iter()
                .map(native::RxComponent::Rx),
        )
}

/// The position of a native component in [`native_components`].
pub(crate) fn native_position(component: native::RxComponent) -> usize {
    match component {
        native::RxComponent::AbA => 0,
        native::RxComponent::AbB => 1,
        native::RxComponent::Rx(index) => {
            2 + native::RxIndex::ALL
                .iter()
                .position(|&listed| listed == index)
                .expect("every native index is listed")
        }
    }
}

/// The nested components in the order their openings are listed.
pub(crate) fn nested_components() -> impl Iterator<Item = nested::RxComponent> {
    [nested::RxComponent::AbA, nested::RxComponent::AbB]
        .into_iter()
        .chain(
            nested::RxIndex::ALL
                .into_iter()
                .map(nested::RxComponent::Rx),
        )
}

/// The position of a nested component in [`nested_components`].
pub(crate) fn nested_position(component: nested::RxComponent) -> usize {
    match component {
        nested::RxComponent::AbA => 0,
        nested::RxComponent::AbB => 1,
        nested::RxComponent::Rx(index) => {
            2 + nested::RxIndex::ALL
                .iter()
                .position(|&listed| listed == index)
                .expect("every nested index is listed")
        }
    }
}

/// The opening claims a reduction leaves over `commitments`, the
/// components' in order: each committed polynomial at $r$ and $rz$, $p$ at
/// $1/r$, $q$ at $r$, and $p$ at $0$, where it must equal `target`.
fn openings<C: CurveAffine>(
    mut commitments: Vec<C>,
    reduction: &Reduction<C>,
    r: C::Scalar,
    z: C::Scalar,
    inverse_r: C::Scalar,
    target: C::Scalar,
) -> Openings<C> {
    let rz = r * z;
    let (p, q) = (commitments.len(), commitments.len() + 1);
    let mut claims = Vec::with_capacity(2 * commitments.len() + 3);
    for (poly, opened) in reduction.openings.iter().enumerate() {
        claims.push(OpeningClaim {
            poly,
            point: r,
            value: opened.at_r,
        });
        claims.push(OpeningClaim {
            poly,
            point: rz,
            value: opened.at_rz,
        });
    }
    claims.push(OpeningClaim {
        poly: p,
        point: inverse_r,
        value: reduction.p_at_inverse_r,
    });
    claims.push(OpeningClaim {
        poly: q,
        point: r,
        value: reduction.q_at_r,
    });
    claims.push(OpeningClaim {
        poly: p,
        point: C::Scalar::ZERO,
        value: target,
    });
    commitments.push(reduction.p);
    commitments.push(reduction.q);
    Openings {
        commitments,
        claims,
    }
}

/// The inverse of a challenge, which is zero with negligible probability.
fn invert<F: Field>(value: F) -> Result<F> {
    Option::from(value.invert())
        .ok_or_else(|| Error::InvalidWitness("a zero challenge cannot be inverted".into()))
}

#[cfg(test)]
#[path = "../../../tests/compress_revdot.rs"]
mod tests;
