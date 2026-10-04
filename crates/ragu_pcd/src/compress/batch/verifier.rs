//! The verifier's side of the batch.

use alloc::vec::Vec;

use ragu_backend::Backend;
use ragu_circuits::polynomials::Rank;
use ragu_core::{Error, FixedGenerators, Result};
use udon::{curve::Affine, field::Field};

use super::{Batch, Batched, check_claims};
use crate::{
    SelectableBackend,
    compress::revdot::Openings,
    ipa::{self, IpaProof, IpaTranscript, MSM, Params},
};

/// Derives the batched commitment, point, and value from `openings` and
/// `batch`, then checks `opening` against that claim through the IPA.
pub(crate) fn verify_openings<P: Affine, R: Rank, B: SelectableBackend>(
    openings: &Openings<P>,
    batch: &Batch<P>,
    opening: &IpaProof<P>,
    generators: &impl FixedGenerators<P>,
    u: P,
    transcript: &mut impl IpaTranscript<P>,
) -> Result<bool> {
    let claim = batch.verify::<B>(openings, transcript)?;
    let params = Params::with_k(generators, u, R::RANK);
    let mut msm = MSM::new(&params);
    msm.append_term(P::Scalar::ONE, claim.commitment);
    Ok(
        ipa::verify_proof(&params, msm, transcript, opening, claim.point, claim.value)?
            .use_challenges()
            .eval::<B>(),
    )
}

impl<C: Affine> Batch<C> {
    /// Derives the claim the IPA must prove for `openings`.
    ///
    /// # Errors
    ///
    /// Fails if claims assign different values to the same polynomial at the
    /// same point, if the batch does not carry one value per polynomial, or if
    /// $u$ lands on a query point, which happens with negligible probability.
    pub(crate) fn verify<B: Backend>(
        &self,
        openings: &Openings<C>,
        transcript: &mut impl IpaTranscript<C>,
    ) -> Result<Batched<C>> {
        let Openings {
            commitments,
            claims,
        } = openings;
        if self.evaluations.len() != commitments.len() {
            return Err(Error::InvalidWitness(
                "one value per batched polynomial".into(),
            ));
        }

        check_claims(claims)?;
        let alpha = transcript.squeeze_challenge()?;
        transcript.write_point(self.f)?;
        let u = transcript.squeeze_challenge()?;
        for &value in &self.evaluations {
            transcript.write_scalar(value)?;
        }
        let beta = transcript.squeeze_challenge()?;

        // f(u) from the quotient relation, the first claim weighted highest.
        let mut f_at_u = C::Scalar::ZERO;
        for claim in claims {
            let denominator = (u - claim.point)
                .invert()
                .ok_or_else(|| Error::InvalidWitness("u lands on a query point".into()))?;
            f_at_u = f_at_u * alpha + (self.evaluations[claim.poly] - claim.value) * denominator;
        }

        // v and the commitment to p: f and every polynomial under beta, f
        // weighted highest.
        let mut value = f_at_u;
        for &evaluation in &self.evaluations {
            value = value * beta + evaluation;
        }
        let mut weights = Vec::with_capacity(commitments.len() + 1);
        let mut weight = C::Scalar::ONE;
        for _ in 0..=commitments.len() {
            weights.push(weight);
            weight *= beta;
        }
        weights.reverse();
        let points: Vec<C> = core::iter::once(self.f)
            .chain(commitments.iter().copied())
            .collect();
        let commitment = B::msm(&weights, &points).into();

        Ok(Batched {
            commitment,
            point: u,
            value,
        })
    }
}
