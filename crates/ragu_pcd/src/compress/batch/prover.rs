//! The prover's side of the batch.

use alloc::{borrow::Cow, boxed::Box, vec::Vec};

use ragu_arithmetic::{CurveAffine, FixedGenerators, factor_iter, ff::Field};
use ragu_circuits::polynomials::{Rank, sparse};
use ragu_core::Result;

use super::Batch;
use crate::{compress::revdot::OpeningClaim, ipa::IpaTranscript};

/// The prover's batch: `polys` are the committed polynomials the `claims`
/// refer to, in the order their commitments are listed. Returns the
/// messages and $p$, the polynomial the IPA opens, with $n$ coefficients.
pub(crate) fn batch<C: CurveAffine, R: Rank, T: IpaTranscript<C>>(
    polys: &[Cow<'_, sparse::Polynomial<C::Scalar, R>>],
    claims: &[OpeningClaim<C::Scalar>],
    generators: &impl FixedGenerators<C>,
    transcript: &mut T,
) -> Result<(Batch<C>, Vec<C::Scalar>)> {
    let alpha = transcript.squeeze_challenge()?;

    // f: the quotients of every claim, batched under alpha.
    let quotients = claims
        .iter()
        .map(|claim| factor_iter(polys[claim.poly].iter_coeffs(), claim.point))
        .collect();
    let f = batched_quotients::<_, R>(quotients, alpha);
    let f_commitment = f.commit_to_affine(generators);
    transcript.write_point(f_commitment)?;

    let u = transcript.squeeze_challenge()?;
    let mut evaluations = Vec::with_capacity(polys.len());
    for poly in polys {
        let value = poly.eval(u);
        transcript.write_scalar(value)?;
        evaluations.push(value);
    }

    // p: f and every polynomial, folded under beta with f weighted highest.
    let beta = transcript.squeeze_challenge()?;
    let mut p = f;
    for poly in polys {
        p.scale(beta);
        p.add_assign(poly);
    }

    Ok((
        Batch {
            f: f_commitment,
            evaluations,
        },
        p.iter_coeffs().collect(),
    ))
}

/// Horner-batches quotient coefficient streams, highest degree first as
/// [`factor_iter`] yields them, under $\alpha$: the first stream receives the
/// highest power.
fn batched_quotients<F: Field, R: Rank>(
    mut streams: Vec<Box<dyn Iterator<Item = F> + '_>>,
    alpha: F,
) -> sparse::Polynomial<F, R> {
    let mut coeffs = Vec::with_capacity(R::num_coeffs());
    let (first, rest) = streams.split_first_mut().expect("at least one claim");
    for coeff in first.by_ref() {
        let batched = rest.iter_mut().fold(coeff, |acc, stream| {
            alpha * acc + stream.next().expect("streams have equal length")
        });
        coeffs.push(batched);
    }
    coeffs.reverse();
    sparse::Polynomial::from_coeffs(coeffs)
}
