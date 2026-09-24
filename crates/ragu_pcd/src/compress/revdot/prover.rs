//! The prover's side of the reduction.

use alloc::{vec, vec::Vec};

use ragu_arithmetic::{
    CurveAffine, Cycle, FixedGenerators, decomp_poly, eval, ff::Field, poly_mul,
};
use ragu_backend::Backend;
use ragu_circuits::{
    polynomials::{Rank, sparse},
    registry::Registry,
};
use ragu_core::Result;

use super::{Reduction, Witness, invert, native_components, nested_components};
use crate::{
    Proof,
    compress::claims::{Masked, NativePolys, NestedPolys, Opened},
    internal::{claims::Builder, native, nested},
    ipa::IpaTranscript,
};

/// The prover's reduction on one curve: `claims` are the $(a_i, b_i)$
/// coefficient vectors in claim order, and `committed` the polynomials to
/// open, in component order.
fn reduce<C: CurveAffine, R: Rank, T: IpaTranscript<C>>(
    claims: impl Iterator<Item = (Vec<C::Scalar>, Vec<C::Scalar>)>,
    committed: &[&sparse::Polynomial<C::Scalar, R>],
    generators: &impl FixedGenerators<C>,
    z: C::Scalar,
    transcript: &mut T,
) -> Result<(Reduction<C>, Witness<C::Scalar>)> {
    let n = R::num_coeffs();
    let rho = transcript.squeeze_challenge()?;

    // t = \sum_i \rho^i a_i b_i
    let mut t = vec![C::Scalar::ZERO; 2 * n - 1];
    let mut product = Vec::new();
    let mut weight = C::Scalar::ONE;
    for (a, b) in claims {
        poly_mul(&a, &b, &mut product);
        for (t, c) in t.iter_mut().zip(&product) {
            *t += weight * c;
        }
        weight *= rho;
    }

    let (p, mut q) = decomp_poly(t, n);
    q.resize(n, C::Scalar::ZERO);
    let commit = |coeffs: &[C::Scalar]| {
        sparse::Polynomial::<_, R>::from_coeffs(coeffs.to_vec()).commit_to_affine(generators)
    };
    let p_commitment = commit(&p);
    let q_commitment = commit(&q);
    transcript.write_point(p_commitment)?;
    transcript.write_point(q_commitment)?;

    let r = transcript.squeeze_challenge()?;
    let inverse_r = invert(r)?;
    let mut openings = Vec::with_capacity(committed.len());
    for poly in committed {
        let opened = Opened {
            at_r: poly.eval(r),
            at_rz: poly.eval(r * z),
        };
        transcript.write_scalar(opened.at_r)?;
        transcript.write_scalar(opened.at_rz)?;
        openings.push(opened);
    }
    let p_at_inverse_r = eval(&p, inverse_r);
    let q_at_r = eval(&q, r);
    transcript.write_scalar(p_at_inverse_r)?;
    transcript.write_scalar(q_at_r)?;

    Ok((
        Reduction {
            p: p_commitment,
            q: q_commitment,
            openings,
            p_at_inverse_r,
            q_at_r,
        },
        Witness { r, p, q },
    ))
}

/// The prover's native reduction of `proof`'s claims at `y` and `z`.
pub(crate) fn reduce_native<C: Cycle, R: Rank, B: Backend, T: IpaTranscript<C::HostCurve>>(
    proof: &Proof<C, R>,
    registry: &Registry<'_, C::CircuitField, R>,
    generators: &C::HostGenerators,
    y: C::CircuitField,
    z: C::CircuitField,
    masked: &[Masked<native::RxComponent, C::CircuitField>],
    transcript: &mut T,
) -> Result<(Reduction<C::HostCurve>, Witness<C::CircuitField>)> {
    let mut builder = Builder::<_, C::CircuitField, R, B>::new(registry, y, z);
    native::claims::build(&NativePolys(proof), &mut builder)?;
    let committed: Vec<_> = native_components()
        .map(|component| &proof[component])
        .collect();
    let claims = builder
        .a
        .iter()
        .zip(&builder.b)
        .map(|(a, b)| (a.iter_coeffs().collect(), b.iter_coeffs().collect()))
        .chain(masked.iter().map(|masked| {
            let mut a = proof[masked.poly].clone();
            a.sub_assign(&masked.expected::<R>());
            (
                a.iter_coeffs().collect(),
                masked.mask::<R>().iter_coeffs().collect(),
            )
        }));
    reduce::<_, R, _>(claims, &committed, generators, z, transcript)
}

/// The prover's nested reduction of `proof`'s claims at the nested `y` and
/// `z`.
pub(crate) fn reduce_nested<C: Cycle, R: Rank, B: Backend, T: IpaTranscript<C::NestedCurve>>(
    proof: &Proof<C, R>,
    registry: &Registry<'_, C::ScalarField, R>,
    generators: &C::NestedGenerators,
    y: C::ScalarField,
    z: C::ScalarField,
    masked: &[Masked<nested::RxComponent, C::ScalarField>],
    transcript: &mut T,
) -> Result<(Reduction<C::NestedCurve>, Witness<C::ScalarField>)> {
    let mut builder = Builder::<_, C::ScalarField, R, B>::new(registry, y, z);
    nested::claims::build(&NestedPolys(proof), &mut builder)?;
    let committed: Vec<_> = nested_components()
        .map(|component| &proof[component])
        .collect();
    let claims = builder
        .a
        .iter()
        .zip(&builder.b)
        .map(|(a, b)| (a.iter_coeffs().collect(), b.iter_coeffs().collect()))
        .chain(masked.iter().map(|masked| {
            let mut a = proof[masked.poly].clone();
            a.sub_assign(&masked.expected::<R>());
            (
                a.iter_coeffs().collect(),
                masked.mask::<R>().iter_coeffs().collect(),
            )
        }));
    reduce::<_, R, _>(claims, &committed, generators, z, transcript)
}
