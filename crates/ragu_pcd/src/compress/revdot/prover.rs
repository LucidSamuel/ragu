//! The prover's side of the reduction.

use alloc::{borrow::Cow, vec, vec::Vec};

use ragu_arithmetic::{
    CurveAffine, Cycle, DeferredField, FixedGenerators, decomp_poly, eval, ff::Field, poly_mul,
};
use ragu_backend::Backend;
use ragu_circuits::{
    polynomials::{Rank, sparse},
    registry::Registry,
};
use ragu_core::Result;

use super::{
    Reduction, Witness,
    fold::{self, Derived, Fold, Layout, Weights, squeeze_pair},
    invert,
};
use crate::{
    Proof,
    compress::claims::{self, Kind, Masked, NativePolys, NestedPolys, Shape},
    internal::{claims::Builder, native, nested},
    ipa::IpaTranscript,
};

/// A revdot claim's polynomials.
type Claim<'a, F, R> = (
    Cow<'a, sparse::Polynomial<F, R>>,
    Cow<'a, sparse::Polynomial<F, R>>,
);

/// $\sum$ `weight` $\cdot$ `poly` over `terms`.
fn combine<'a, F: Field, R: Rank>(
    terms: impl Iterator<Item = (F, &'a sparse::Polynomial<F, R>)>,
) -> sparse::Polynomial<F, R> {
    let mut acc = sparse::Polynomial::default();
    for (weight, poly) in terms {
        let mut term = poly.clone();
        term.scale(weight);
        acc.add_assign(&term);
    }
    acc
}

/// $\sum_i x^i$ `polys`$_i$.
fn fold_powers<'a, F: Field, R: Rank>(
    polys: impl DoubleEndedIterator<Item = &'a sparse::Polynomial<F, R>>,
    x: F,
) -> sparse::Polynomial<F, R> {
    sparse::Polynomial::fold(polys.rev(), x)
}

/// The products `pairs` index into `a` and `b`, as the low coefficients of
/// one polynomial.
fn errors<'a, F: DeferredField, R: Rank, B: Backend>(
    a: impl Fn(usize) -> &'a sparse::Polynomial<F, R>,
    b: impl Fn(usize) -> &'a sparse::Polynomial<F, R>,
    pairs: impl Iterator<Item = (usize, usize)>,
) -> sparse::Polynomial<F, R> {
    sparse::Polynomial::from_coeffs(pairs.map(|(i, j)| B::sparse_revdot(a(i), b(j))).collect())
}

/// What the fold leaves the split: its messages, the three folded claims,
/// the [`Derived`] polynomials and their commitments.
type Folded<C, R> = (
    Fold<C>,
    Vec<Claim<'static, <C as CurveAffine>::ScalarExt, R>>,
    Vec<sparse::Polynomial<<C as CurveAffine>::ScalarExt, R>>,
    Vec<C>,
);

/// The prover's fold on one curve, over `claims` in claim order with their
/// `shapes`: commits each layer's error terms and squeezes its weights.
fn fold_claims<C: CurveAffine, R: Rank, B: Backend, Id: Copy, T: IpaTranscript<C>>(
    claims: &[Claim<'_, C::Scalar, R>],
    shapes: &[Shape<Id, C::Scalar>],
    masked: &[Masked<Id, C::Scalar>],
    commitment: impl Fn(Id) -> C,
    generators: &impl FixedGenerators<C>,
    transcript: &mut T,
) -> Result<Folded<C, R>>
where
    C::Scalar: DeferredField,
{
    let layout = Layout::new(claims.len());

    // The first layer: the error terms within each group, then the groups
    // folded.
    let inner = errors::<_, R, B>(
        |i| claims[i].0.as_ref(),
        |j| claims[j].1.as_ref(),
        layout
            .inner()
            .map(|(g, i, j)| (g * fold::GROUP + i, g * fold::GROUP + j)),
    );
    let inner_commitment = inner.commit_to_affine(generators);
    transcript.write_point(inner_commitment)?;
    let (mu, nu) = squeeze_pair(transcript)?;
    let groups: Vec<(sparse::Polynomial<_, R>, sparse::Polynomial<_, R>)> = (0..layout.groups())
        .map(|g| {
            let members = &claims[layout.members(g)];
            (
                fold_powers(members.iter().map(|(a, _)| a.as_ref()), mu),
                fold_powers(members.iter().map(|(_, b)| b.as_ref()), nu),
            )
        })
        .collect();

    // The second layer, over the groups.
    let outer = errors::<_, R, B>(|g| &groups[g].0, |h| &groups[h].1, layout.outer());
    let outer_commitment = outer.commit_to_affine(generators);
    transcript.write_point(outer_commitment)?;
    let (mu_prime, nu_prime) = squeeze_pair(transcript)?;
    let a = fold_powers(groups.iter().map(|(a, _)| a), mu_prime);
    let b = fold_powers(groups.iter().map(|(_, b)| b), nu_prime);

    // The weighted error terms, as revdots against the public weights.
    let weights = Weights {
        mu,
        nu,
        mu_prime,
        nu_prime,
    };
    let inner_weights = weights.inner::<R>(&layout);
    let outer_weights = weights.outer::<R>(&layout);
    let inner_epsilon = B::sparse_revdot(&inner, &inner_weights);
    let outer_epsilon = B::sparse_revdot(&outer, &outer_weights);
    transcript.write_scalar(inner_epsilon)?;
    transcript.write_scalar(outer_epsilon)?;
    let messages = Fold {
        inner: inner_commitment,
        outer: outer_commitment,
        inner_epsilon,
        outer_epsilon,
    };

    // The derived polynomials. A's committed part adds back the wire
    // bindings' expected values, which their a subtracted.
    let mut committed_a = a.clone();
    for (i, shape) in shapes.iter().enumerate() {
        if let Kind::Masked(m) = shape.kind {
            let mut expected = masked[m].expected::<R>();
            expected.scale(weights.a(i));
            committed_a.add_assign(&expected);
        }
    }
    let of_kind = |kinds: fn(Kind) -> bool| {
        shapes
            .iter()
            .enumerate()
            .filter(move |(_, shape)| kinds(shape.kind))
            .map(|(i, _)| i)
    };
    let dilated = combine(
        of_kind(|kind| matches!(kind, Kind::Circuit(_)))
            .map(|i| (weights.b(i), claims[i].0.as_ref())),
    );
    let raw = combine(
        of_kind(|kind| matches!(kind, Kind::Raw)).map(|i| (weights.b(i), claims[i].1.as_ref())),
    );
    let commitments = fold::commitments(shapes, &weights, commitment, &messages);

    Ok((
        messages,
        vec![
            (Cow::Owned(a), Cow::Owned(b)),
            (Cow::Owned(inner.clone()), Cow::Owned(inner_weights)),
            (Cow::Owned(outer.clone()), Cow::Owned(outer_weights)),
        ],
        vec![committed_a, dilated, raw, inner, outer],
        commitments,
    ))
}

/// The prover's reduction on one curve: `claims` are the $(a_i, b_i)$ in
/// claim order and `shapes` their shapes, `masked` the wire bindings the
/// claims end with, and `commitment` gives each component's commitment.
fn reduce<C: CurveAffine, R: Rank, B: Backend, Id: Copy, T: IpaTranscript<C>>(
    claims: &[Claim<'_, C::Scalar, R>],
    shapes: &[Shape<Id, C::Scalar>],
    masked: &[Masked<Id, C::Scalar>],
    commitment: impl Fn(Id) -> C,
    generators: &impl FixedGenerators<C>,
    z: C::Scalar,
    transcript: &mut T,
) -> Result<(Reduction<C>, Witness<C, R>)>
where
    C::Scalar: DeferredField,
{
    let n = R::num_coeffs();
    let (messages, folded, derived, commitments) =
        fold_claims::<C, R, B, Id, T>(claims, shapes, masked, commitment, generators, transcript)?;
    let rho = transcript.squeeze_challenge()?;

    // t = \sum_i \rho^i a_i b_i over the folded claims.
    let mut t = vec![C::Scalar::ZERO; 2 * n - 1];
    let mut product = Vec::new();
    let mut weight = C::Scalar::ONE;
    for (a, b) in &folded {
        let (a, b): (Vec<_>, Vec<_>) = (a.iter_coeffs().collect(), b.iter_coeffs().collect());
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
    let mut openings = Vec::with_capacity(derived.len());
    for (which, poly) in Derived::ALL.iter().zip(&derived) {
        let opened = poly.eval(which.point(r, z));
        transcript.write_scalar(opened)?;
        openings.push(opened);
    }
    let p_at_inverse_r = eval(&p, inverse_r);
    let q_at_r = eval(&q, r);
    transcript.write_scalar(p_at_inverse_r)?;
    transcript.write_scalar(q_at_r)?;

    Ok((
        Reduction {
            fold: messages,
            p: p_commitment,
            q: q_commitment,
            openings,
            p_at_inverse_r,
            q_at_r,
        },
        Witness {
            r,
            p,
            q,
            derived,
            commitments,
        },
    ))
}

/// The `masked` wire claims as $(Q - E, M)$ over the stage polynomials
/// `poly` gives.
fn masked_claims<'a, F: Field, R: Rank, Id: Copy>(
    poly: impl Fn(Id) -> &'a sparse::Polynomial<F, R>,
    masked: &[Masked<Id, F>],
) -> impl Iterator<Item = Claim<'a, F, R>> {
    masked.iter().map(move |masked| {
        let mut a = poly(masked.poly).clone();
        a.sub_assign(&masked.expected::<R>());
        (Cow::Owned(a), Cow::Owned(masked.mask::<R>()))
    })
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
) -> Result<(Reduction<C::HostCurve>, Witness<C::HostCurve, R>)> {
    let mut builder = Builder::<_, C::CircuitField, R, B>::new(registry, y, z);
    native::claims::build(&NativePolys(proof), &mut builder)?;
    let claims: Vec<_> = builder
        .a
        .into_iter()
        .zip(builder.b)
        .chain(masked_claims(|component| &proof[component], masked))
        .collect();
    let shapes = claims::native_shapes(proof.circuit_id(), z, masked)?;
    reduce::<_, R, B, _, _>(
        &claims,
        &shapes,
        masked,
        |component| proof.native_commitment(component),
        generators,
        z,
        transcript,
    )
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
) -> Result<(Reduction<C::NestedCurve>, Witness<C::NestedCurve, R>)> {
    let mut builder = Builder::<_, C::ScalarField, R, B>::new(registry, y, z);
    nested::claims::build(&NestedPolys(proof), &mut builder)?;
    let claims: Vec<_> = builder
        .a
        .into_iter()
        .zip(builder.b)
        .chain(masked_claims(|component| &proof[component], masked))
        .collect();
    let shapes = claims::nested_shapes(z, masked)?;
    reduce::<_, R, B, _, _>(
        &claims,
        &shapes,
        masked,
        |component| match component {
            nested::RxComponent::AbA => proof.nested_a_commitment(),
            nested::RxComponent::AbB => proof.nested_b_commitment(),
            nested::RxComponent::Rx(index) => proof.nested_rx_commitment(index),
        },
        generators,
        z,
        transcript,
    )
}
