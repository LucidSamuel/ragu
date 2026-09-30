//! The verifier's side of the batch.

use alloc::vec::Vec;

use ragu_core::{Error, Result};
use udon::{curve::Affine, field::Field};

use super::{Batch, Batched, check_claims};
use crate::{compress::revdot::OpeningClaim, ipa::IpaTranscript};

/// The verifier's batch: `commitments` are the polynomials the `claims`
/// refer to. Returns the claim the IPA must prove.
///
/// # Errors
///
/// Fails if claims assign different values to the same polynomial at the
/// same point, if the batch does not carry one value per polynomial, or if
/// $u$ lands on a query point, which happens with negligible probability.
pub(crate) fn verify<C: Affine, T: IpaTranscript<C>>(
    commitments: &[C],
    claims: &[OpeningClaim<C::Scalar>],
    batch: &Batch<C>,
    transcript: &mut T,
) -> Result<Batched<C>> {
    if batch.evaluations.len() != commitments.len() {
        return Err(Error::InvalidWitness(
            "one value per batched polynomial".into(),
        ));
    }

    check_claims(claims)?;
    let alpha = transcript.squeeze_challenge()?;
    transcript.write_point(batch.f)?;
    let u = transcript.squeeze_challenge()?;
    for &value in &batch.evaluations {
        transcript.write_scalar(value)?;
    }
    let beta = transcript.squeeze_challenge()?;

    // f(u) from the quotient relation, the first claim weighted highest.
    let mut f_at_u = C::Scalar::ZERO;
    for claim in claims {
        let denominator = (u - claim.point)
            .invert()
            .ok_or_else(|| Error::InvalidWitness("u lands on a query point".into()))?;
        f_at_u = f_at_u * alpha + (batch.evaluations[claim.poly] - claim.value) * denominator;
    }

    // v and the commitment to p: f and every polynomial under beta, f
    // weighted highest.
    let mut value = f_at_u;
    for &evaluation in &batch.evaluations {
        value = value * beta + evaluation;
    }
    let mut weights = Vec::with_capacity(commitments.len() + 1);
    let mut weight = C::Scalar::ONE;
    for _ in 0..=commitments.len() {
        weights.push(weight);
        weight *= beta;
    }
    weights.reverse();
    let points: Vec<C> = core::iter::once(batch.f)
        .chain(commitments.iter().copied())
        .collect();
    let commitment = C::msm(&weights, &points).into();

    Ok(Batched {
        commitment,
        point: u,
        value,
    })
}
