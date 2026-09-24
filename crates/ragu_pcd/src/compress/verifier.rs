//! The verifier's side of the compression: [`Application::verify_compressed`].

use ragu_arithmetic::{CurveAffine, Cycle, FixedGenerators, ff::Field};
use ragu_circuits::polynomials::Rank;
use ragu_core::Result;

use super::{
    CompressedPcd, Sampled,
    batch::{self, Batch},
    revdot::{self, Openings},
    transcript,
};
use crate::{
    Application, RAGU_TAG, SelectableBackend,
    header::Header,
    internal::ky,
    ipa::{self, CycleTranscript, IpaProof, IpaTranscript, MSM, Params},
};

/// The backend whose kernels [`Application::verify_compressed`] consults for
/// the selected backend `B`, as [`Application::verify`] does.
type Verifier<B> = <B as SelectableBackend>::Verifier;

/// Derives the batched claim of `openings` from `batch` and checks `opening`
/// against it through the IPA, on one curve.
fn check<P: CurveAffine, R: Rank, T: IpaTranscript<P>>(
    openings: &Openings<P>,
    batch: &Batch<P>,
    opening: &IpaProof<P>,
    generators: &impl FixedGenerators<P>,
    transcript: &mut T,
) -> Result<bool> {
    let claim = batch::verify(&openings.commitments, &openings.claims, batch, transcript)?;
    let params = Params::with_k(generators, R::RANK);
    let mut msm = MSM::new(&params);
    msm.append_term(P::Scalar::ONE, claim.commitment);
    Ok(
        ipa::verify_proof(&params, msm, transcript, opening, claim.point, claim.value)?
            .use_challenges()
            .eval(),
    )
}

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize, B: SelectableBackend>
    Application<'_, C, R, HEADER_SIZE, B>
{
    /// Verifies some [`CompressedPcd`] for the provided [`Header`].
    ///
    /// Returns `Ok(true)` if every check passes, `Ok(false)` if any fails
    /// (an invalid circuit id, a malformed proof, a rejected reduction or
    /// opening), or `Err` if an internal computation error occurs.
    ///
    /// The computational kernels are those of the sealed
    /// [`SelectableBackend::Verifier`] of the selected backend, as for
    /// [`verify`](Self::verify).
    pub fn verify_compressed<H: Header<C::CircuitField>>(
        &self,
        pcd: &CompressedPcd<C, H>,
    ) -> Result<bool> {
        let proof = pcd.proof();
        let instance = &proof.instance;

        // The proof's circuit_id must be in the registry's domain, for the
        // reason `verify` gives, and the headers must have the declared
        // size; and the messages must have the shape read below.
        if !self.native_registry.circuit_in_domain(instance.circuit_id)
            || instance.left_header.len() != HEADER_SIZE
            || instance.right_header.len() != HEADER_SIZE
            || !proof.well_formed::<R>()
        {
            return Ok(false);
        }

        // The fuse's challenges, from the bridge commitments in the fuse's
        // schedule, with pre_beta in the endoscalar range; and the nested
        // stages the decider recomputes from public data.
        let Some(challenges) =
            instance.challenges(&mut CycleTranscript::<C>::new(self.params, RAGU_TAG)?)?
        else {
            return Ok(false);
        };
        if !instance.stages_match::<R, Verifier<B>, HEADER_SIZE>(
            &challenges,
            C::nested_generators(self.params),
        )? {
            return Ok(false);
        }

        let output_header = ky::output_header::<C, H, HEADER_SIZE>(pcd.data().clone())?;
        let mut transcript = transcript(self.params, instance, &output_header)?;
        let native_sampled = Sampled::squeeze(&mut transcript.host())?;
        let nested_sampled = Sampled::squeeze(&mut transcript.nested())?;
        let (native_targets, nested_targets) = instance.targets::<HEADER_SIZE>(
            &challenges,
            &output_header,
            native_sampled.y,
            nested_sampled.y,
        )?;

        let native = {
            let registry = &self.native_registry;
            let Sampled { w, y, z, sigma } = native_sampled;
            let masked = instance.native_bindings::<R, Verifier<B>, HEADER_SIZE>(
                &challenges,
                registry,
                sigma,
            )?;
            let Some(mut openings) = revdot::verify_native::<C, R, Verifier<B>, _>(
                instance.circuit_id,
                |component| instance.native_commitment(component),
                registry,
                y,
                z,
                &native_targets,
                &masked,
                &proof.native.reduction,
                &mut transcript.host(),
            )?
            else {
                return Ok(false);
            };
            let (commitments, claims) = instance.native_openings::<R, Verifier<B>>(
                &challenges,
                registry,
                w,
                openings.commitments.len(),
            );
            openings.commitments.extend(commitments);
            openings.claims.extend(claims);
            check::<_, R, _>(
                &openings,
                &proof.native.batch,
                &proof.native.opening,
                C::host_generators(self.params),
                &mut transcript.host(),
            )?
        };
        if !native {
            return Ok(false);
        }

        let nested = {
            let registry = &self.nested_registry;
            let Sampled { w, y, z, sigma } = nested_sampled;
            let masked =
                instance.nested_bindings::<R, Verifier<B>>(&challenges, registry, sigma)?;
            let Some(mut openings) = revdot::verify_nested::<C, R, Verifier<B>, _>(
                |component| instance.nested_commitment(component),
                registry,
                y,
                z,
                &nested_targets,
                &masked,
                &proof.nested.reduction,
                &mut transcript.nested(),
            )?
            else {
                return Ok(false);
            };
            let (commitments, claims) = instance.nested_openings::<R, Verifier<B>>(
                &challenges,
                registry,
                w,
                openings.commitments.len(),
            )?;
            openings.commitments.extend(commitments);
            openings.claims.extend(claims);
            check::<_, R, _>(
                &openings,
                &proof.nested.batch,
                &proof.nested.opening,
                C::nested_generators(self.params),
                &mut transcript.nested(),
            )?
        };
        Ok(nested)
    }
}
