//! The verifier's side of the reduction.

use alloc::vec::Vec;

use ragu_arithmetic::{CurveAffine, Cycle, ff::Field};
use ragu_backend::Backend;
use ragu_circuits::{
    polynomials::Rank,
    registry::{CircuitIndex, Registry},
};
use ragu_core::{Error, Result};

use super::{
    Openings, Reduction, invert, native_components, native_position, nested_components,
    nested_position, openings,
};
use crate::{
    compress::claims::{self, Evaluated, Masked, Opened},
    internal::{
        ky::{NativeKy, NestedKy},
        native, nested,
    },
    ipa::IpaTranscript,
};

/// The verifier's side on one curve: `evaluate` gives the claims at $r$ from
/// the claimed openings, and `commitments` are the committed polynomials in
/// component order. Returns the opening claims the batch must prove, or
/// `None` if the reduction does not hold.
fn verify<C: CurveAffine, R: Rank, T: IpaTranscript<C>>(
    evaluate: impl FnOnce(C::Scalar, &[Opened<C::Scalar>]) -> Result<Vec<Evaluated<C::Scalar>>>,
    commitments: Vec<C>,
    reduction: &Reduction<C>,
    z: C::Scalar,
    transcript: &mut T,
) -> Result<Option<Openings<C>>> {
    let n = R::num_coeffs();
    if reduction.openings.len() != commitments.len() {
        return Err(Error::InvalidWitness(
            "one pair of openings per committed polynomial".into(),
        ));
    }

    let rho = transcript.squeeze_challenge()?;
    transcript.write_point(reduction.p)?;
    transcript.write_point(reduction.q)?;
    let r = transcript.squeeze_challenge()?;
    let inverse_r = invert(r)?;
    for opened in &reduction.openings {
        transcript.write_scalar(opened.at_r)?;
        transcript.write_scalar(opened.at_rz)?;
    }
    transcript.write_scalar(reduction.p_at_inverse_r)?;
    transcript.write_scalar(reduction.q_at_r)?;

    // \sum_i \rho^i a_i(r) b_i(r) against the split, and the target p(0)
    // must take.
    let evaluated = evaluate(r, &reduction.openings)?;
    let (mut combined, mut target, mut weight) = (C::Scalar::ZERO, C::Scalar::ZERO, C::Scalar::ONE);
    for claim in &evaluated {
        combined += weight * claim.a * claim.b;
        target += weight * claim.k;
        weight *= rho;
    }
    let split = r.pow_vartime([(n - 1) as u64]) * reduction.p_at_inverse_r
        + r.pow_vartime([n as u64]) * reduction.q_at_r;
    if combined != split {
        return Ok(None);
    }

    Ok(Some(openings(
        commitments,
        reduction,
        r,
        z,
        inverse_r,
        target,
    )))
}

/// The verifier's native side: `commitment` gives each component's
/// commitment, `registry` the native registry, and `targets` the claims'
/// $k(y)$ values; the registry is read through the backend `B`.
pub(crate) fn verify_native<C: Cycle, R: Rank, B: Backend, T: IpaTranscript<C::HostCurve>>(
    circuit_id: CircuitIndex,
    commitment: impl Fn(native::RxComponent) -> C::HostCurve,
    registry: &Registry<'_, C::CircuitField, R>,
    y: C::CircuitField,
    z: C::CircuitField,
    targets: &NativeKy<C::CircuitField>,
    masked: &[Masked<native::RxComponent, C::CircuitField>],
    reduction: &Reduction<C::HostCurve>,
    transcript: &mut T,
) -> Result<Option<Openings<C::HostCurve>>> {
    let commitments: Vec<_> = native_components().map(commitment).collect();
    verify::<_, R, _>(
        |r, openings| {
            claims::native::<R, _>(
                circuit_id,
                r,
                z,
                |component| openings[native_position(component)],
                |circuit| B::sparse_eval(&B::registry_circuit_y(registry, circuit, y), r),
                targets,
                masked,
            )
        },
        commitments,
        reduction,
        z,
        transcript,
    )
}

/// The verifier's nested side, as [`verify_native`] takes its inputs.
pub(crate) fn verify_nested<C: Cycle, R: Rank, B: Backend, T: IpaTranscript<C::NestedCurve>>(
    commitment: impl Fn(nested::RxComponent) -> C::NestedCurve,
    registry: &Registry<'_, C::ScalarField, R>,
    y: C::ScalarField,
    z: C::ScalarField,
    targets: &NestedKy<C::ScalarField>,
    masked: &[Masked<nested::RxComponent, C::ScalarField>],
    reduction: &Reduction<C::NestedCurve>,
    transcript: &mut T,
) -> Result<Option<Openings<C::NestedCurve>>> {
    let commitments: Vec<_> = nested_components().map(commitment).collect();
    verify::<_, R, _>(
        |r, openings| {
            claims::nested::<R, _>(
                r,
                z,
                |component| openings[nested_position(component)],
                |circuit| B::sparse_eval(&B::registry_circuit_y(registry, circuit, y), r),
                targets,
                masked,
            )
        },
        commitments,
        reduction,
        z,
        transcript,
    )
}
