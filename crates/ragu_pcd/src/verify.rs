//! This module provides the [`Application::verify`] method implementation.

use core::iter::once;

use ff::Field;
use ragu_arithmetic::Cycle;
use ragu_circuits::{
    polynomials::{Rank, sparse},
    registry::CircuitIndex,
};
use ragu_core::{Result, drivers::emulator::Emulator, maybe::Maybe};
use ragu_primitives::Element;
use rand::CryptoRng;

use crate::{
    Application, Pcd, Proof,
    header::Header,
    internal::{
        claims,
        native::{claims as native_claims, stages::preamble::ProofInputs},
        nested::claims as nested_claims,
    },
};

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    /// Verifies some [`Pcd`] for the provided [`Header`].
    ///
    /// Returns `Ok(true)` if all verification checks pass, `Ok(false)` if
    /// any check fails (e.g., invalid circuit ID, header size mismatch,
    /// corrupted commitments or evaluations), or `Err` if an internal
    /// computation error occurs.
    pub fn verify<RNG: CryptoRng, H: Header<C::CircuitField>>(
        &self,
        pcd: &Pcd<C, R, H>,
        mut rng: RNG,
    ) -> Result<bool> {
        // Sample verification challenges w, y, and z.
        let w = C::CircuitField::random(&mut rng);
        let y = C::CircuitField::random(&mut rng);
        let z = C::CircuitField::random(&mut rng);

        // Validate that the application circuit_id is within the registry domain.
        // (Internal circuit IDs are constants and don't need this check.)
        if !self
            .native_registry
            .circuit_in_domain(pcd.proof().circuit_id())
        {
            return Ok(false);
        }

        // Validate that the `left_header` and `right_header` lengths match
        // `HEADER_SIZE`. Alternatively, the `Proof` structure could be
        // parameterized on the `HEADER_SIZE`, but this appeared to be simpler.
        if pcd.proof().left_header().len() != HEADER_SIZE
            || pcd.proof().right_header().len() != HEADER_SIZE
        {
            return Ok(false);
        }

        // Compute unified k(y), unified_bridge k(y), and application k(y).
        let (unified_ky, unified_bridge_ky, application_ky) =
            Emulator::emulate_wireless((pcd.proof(), pcd.data().clone(), y), |dr, witness| {
                let (proof, data, y) = witness.cast();
                let y = Element::alloc(dr, y)?;
                let proof_inputs =
                    ProofInputs::<_, C, HEADER_SIZE>::alloc_for_verify::<R, H>(dr, proof, data)?;

                let (unified_ky, unified_bridge_ky) = proof_inputs.unified_ky_values(dr, &y)?;
                let unified_ky = *unified_ky.value().take();
                let unified_bridge_ky = *unified_bridge_ky.value().take();
                let application_ky = *proof_inputs.application_ky(dr, &y)?.value().take();

                Ok((unified_ky, unified_bridge_ky, application_ky))
            })?;

        // Build a and b polynomials for each revdot claim.
        let source = native::SingleProofSource { proof: pcd.proof() };
        let mut builder = claims::Builder::new(&self.native_registry, y, z);
        native_claims::build(&source, &mut builder)?;

        // Check all native revdot claims.
        let native_revdot_claims = {
            let ky_source = native::SingleProofKySource {
                // NOTE: `raw_c` is now computed as `revdot(a, b)` rather
                // than stored in the proof, so this claim is tautological
                // in the verifier. It remains meaningful inside the circuit
                // where `c` is an independently allocated witness element.
                raw_c: pcd.proof().c(),
                application_ky,
                unified_bridge_ky,
                unified_ky,
            };

            native::ky_values(&ky_source)
                .zip(builder.a.iter().zip(builder.b.iter()))
                .all(|(ky, (a, b))| a.revdot(b) == ky)
        };

        // Check all nested revdot claims.
        let nested_revdot_claims = {
            let nested_source = nested::SingleProofSource { proof: pcd.proof() };
            let y_nested = C::ScalarField::random(&mut rng);
            let z_nested = C::ScalarField::random(&mut rng);
            let mut nested_builder =
                claims::Builder::new(&self.nested_registry, y_nested, z_nested);
            nested_claims::build(&nested_source, &mut nested_builder)?;

            let ky_source = nested::SingleProofKySource::<C::ScalarField>::new();
            nested::ky_values(&ky_source)
                .zip(nested_builder.a.iter().zip(nested_builder.b.iter()))
                .all(|(ky, (a, b))| a.revdot(b) == ky)
        };

        // Check registry_xy polynomial evaluation at the sampled w.
        // registry_xy_poly is m(W, x, y) - the registry evaluated at current x, y, free in W.
        let registry_xy_claim = {
            let x = pcd.proof().x();
            let y = pcd.proof().y();
            let poly_eval = pcd.proof().native_registry_xy_poly().eval(w);
            let expected = self.native_registry.wxy(w, x, y);
            poly_eval == expected
        };

        // TODO: Add checks for registry_wx0_poly, registry_wx1_poly, and registry_wy_poly.
        // - registry_wx0/wx1: need child proof x challenges (x₀, x₁) which "disappear" in preamble
        // - registry_wy: interstitial value that will be elided later

        Ok(native_revdot_claims && nested_revdot_claims && registry_xy_claim)
    }
}

mod native {
    use super::*;
    pub use crate::internal::native::claims::ky_values;
    use crate::internal::{
        claims::Source,
        native::{RxComponent, claims::KySource},
    };

    pub struct SingleProofSource<'rx, C: Cycle, R: Rank> {
        pub proof: &'rx Proof<C, R>,
    }

    impl<'rx, C: Cycle, R: Rank> Source for SingleProofSource<'rx, C, R> {
        type RxComponent = RxComponent;
        type Rx = &'rx sparse::Polynomial<C::CircuitField, R>;
        type AppCircuitId = CircuitIndex;

        fn rx(&self, component: RxComponent) -> impl Iterator<Item = Self::Rx> {
            core::iter::once(&self.proof[component])
        }

        fn app_circuits(&self) -> impl Iterator<Item = Self::AppCircuitId> {
            core::iter::once(self.proof.circuit_id())
        }
    }

    /// Source for k(y) values for single-proof verification.
    pub struct SingleProofKySource<F> {
        pub raw_c: F,
        pub application_ky: F,
        pub unified_bridge_ky: F,
        pub unified_ky: F,
    }

    impl<F: Field> KySource for SingleProofKySource<F> {
        type Ky = F;

        fn raw_c(&self) -> impl Iterator<Item = F> {
            once(self.raw_c)
        }

        fn application_ky(&self) -> impl Iterator<Item = F> {
            once(self.application_ky)
        }

        fn unified_bridge_ky(&self) -> impl Iterator<Item = F> {
            once(self.unified_bridge_ky)
        }

        fn unified_ky(&self) -> impl Iterator<Item = F> + Clone {
            once(self.unified_ky)
        }

        fn zero(&self) -> F {
            F::ZERO
        }
    }
}

mod nested {
    use super::*;
    pub use crate::internal::nested::claims::ky_values;
    use crate::internal::{
        claims::Source,
        nested::{RxIndex, claims::KySource},
    };

    /// Source for nested field rx polynomials for single-proof verification.
    pub struct SingleProofSource<'rx, C: Cycle, R: Rank> {
        pub proof: &'rx Proof<C, R>,
    }

    impl<'rx, C: Cycle, R: Rank> Source for SingleProofSource<'rx, C, R> {
        type RxComponent = RxIndex;
        type Rx = &'rx sparse::Polynomial<C::ScalarField, R>;
        type AppCircuitId = ();

        fn rx(&self, component: RxIndex) -> impl Iterator<Item = Self::Rx> {
            core::iter::once(&self.proof[component])
        }

        fn app_circuits(&self) -> impl Iterator<Item = Self::AppCircuitId> {
            core::iter::empty()
        }
    }

    /// Source for k(y) values for nested single-proof verification.
    pub struct SingleProofKySource<F>(core::marker::PhantomData<F>);

    impl<F> SingleProofKySource<F> {
        pub fn new() -> Self {
            Self(core::marker::PhantomData)
        }
    }

    impl<F: Field> KySource for SingleProofKySource<F> {
        type Ky = F;

        fn one(&self) -> F {
            F::ONE
        }

        fn zero(&self) -> F {
            F::ZERO
        }
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use ragu_arithmetic::{Cycle, FixedGenerators};
    use ragu_circuits::polynomials::ProductionRank;
    use ragu_pasta::Pasta;
    use ragu_primitives::{GadgetExt, Point};
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::ApplicationBuilder;
    use crate::step::internal::trivial::Trivial;

    type CF = <Pasta as Cycle>::CircuitField;
    type NestedCurve = <Pasta as Cycle>::NestedCurve;
    type TestR = ProductionRank;
    const HEADER_SIZE: usize = 4;

    fn create_test_app() -> crate::Application<'static, Pasta, TestR, HEADER_SIZE> {
        let pasta = Pasta::baked();
        ApplicationBuilder::<Pasta, TestR, HEADER_SIZE>::new()
            .finalize(pasta)
            .expect("failed to create test application")
    }

    fn create_seeded_proof(
        seed: u64,
    ) -> (
        crate::Application<'static, Pasta, TestR, HEADER_SIZE>,
        crate::proof::Proof<Pasta, TestR>,
    ) {
        let app = create_test_app();
        let mut rng = StdRng::seed_from_u64(seed);
        let (pcd, _aux) = app
            .seed(&mut rng, Trivial::new(), ())
            .expect("seeded proof should not fail");
        let (proof, _data) = pcd.into_parts();
        (app, proof)
    }

    #[test]
    fn verify_accepts_seeded_proof() {
        let (app, proof) = create_seeded_proof(42);
        let mut rng = StdRng::seed_from_u64(9999);
        let pcd = proof.carry::<()>(());
        let result = app.verify(&pcd, &mut rng).expect("verify should not error");
        assert!(result, "a freshly seeded proof must be accepted");
    }

    #[test]
    fn verify_transcript_replay_challenges_match() {
        let pasta = Pasta::baked();
        let (_app, proof) = create_seeded_proof(7);

        let dr = &mut ragu_core::drivers::emulator::Emulator::execute();
        let poseidon = Pasta::circuit_poseidon(pasta);
        let mut t = crate::internal::transcript::Transcript::new(dr, poseidon, crate::RAGU_TAG)
            .expect("transcript init should not fail");

        let preamble_commit =
            Point::<_, NestedCurve>::constant(dr, proof.bridge_preamble_commitment())
                .expect("point constant should not fail");
        preamble_commit
            .write(dr, &mut t)
            .expect("write should not fail");
        let w = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();

        let s_prime_commit =
            Point::<_, NestedCurve>::constant(dr, proof.bridge_s_prime_commitment())
                .expect("point constant should not fail");
        s_prime_commit
            .write(dr, &mut t)
            .expect("write should not fail");
        let y = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();
        let z = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();

        let inner_error_commit =
            Point::<_, NestedCurve>::constant(dr, proof.bridge_inner_error_commitment())
                .expect("point constant should not fail");
        inner_error_commit
            .write(dr, &mut t)
            .expect("write should not fail");
        let mu = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();
        let nu = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();

        let outer_error_commit =
            Point::<_, NestedCurve>::constant(dr, proof.bridge_outer_error_commitment())
                .expect("point constant should not fail");
        outer_error_commit
            .write(dr, &mut t)
            .expect("write should not fail");
        let mu_prime = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();
        let nu_prime = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();

        let ab_commit = Point::<_, NestedCurve>::constant(dr, proof.bridge_ab_commitment())
            .expect("point constant should not fail");
        ab_commit.write(dr, &mut t).expect("write should not fail");
        let x = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();

        let query_commit = Point::<_, NestedCurve>::constant(dr, proof.bridge_query_commitment())
            .expect("point constant should not fail");
        query_commit
            .write(dr, &mut t)
            .expect("write should not fail");
        let alpha = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();

        let f_commit = Point::<_, NestedCurve>::constant(dr, proof.bridge_f_commitment())
            .expect("point constant should not fail");
        f_commit.write(dr, &mut t).expect("write should not fail");
        let u = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();

        let eval_commit = Point::<_, NestedCurve>::constant(dr, proof.bridge_eval_commitment())
            .expect("point constant should not fail");
        eval_commit
            .write(dr, &mut t)
            .expect("write should not fail");
        let pre_beta = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();

        assert_eq!(w, proof.w, "w mismatch");
        assert_eq!(y, proof.y, "y mismatch");
        assert_eq!(z, proof.z, "z mismatch");
        assert_eq!(mu, proof.mu, "mu mismatch");
        assert_eq!(nu, proof.nu, "nu mismatch");
        assert_eq!(mu_prime, proof.mu_prime, "mu_prime mismatch");
        assert_eq!(nu_prime, proof.nu_prime, "nu_prime mismatch");
        assert_eq!(x, proof.x, "x mismatch");
        assert_eq!(alpha, proof.alpha, "alpha mismatch");
        assert_eq!(u, proof.u, "u mismatch");
        assert_eq!(pre_beta, proof.pre_beta, "pre_beta mismatch");
    }

    macro_rules! seeded_rejects {
        ($test_name:ident, $seed:expr, |$proof:ident| $corrupt:expr) => {
            #[test]
            fn $test_name() {
                let (app, mut $proof) = create_seeded_proof($seed);
                $corrupt;
                let mut rng = StdRng::seed_from_u64(99999);
                let pcd = $proof.carry::<()>(());
                let result = app.verify(&pcd, &mut rng).expect("verify should not error");
                assert!(
                    !result,
                    concat!(stringify!($test_name), ": verifier must reject")
                );
            }
        };
    }

    seeded_rejects!(rejects_corrupt_w_challenge, 1, |proof| {
        proof.w = CF::random(&mut StdRng::seed_from_u64(777))
    });

    seeded_rejects!(rejects_corrupt_y_challenge, 2, |proof| {
        proof.y = CF::random(&mut StdRng::seed_from_u64(778))
    });

    seeded_rejects!(rejects_corrupt_z_challenge, 3, |proof| {
        proof.z = CF::random(&mut StdRng::seed_from_u64(779))
    });

    seeded_rejects!(rejects_corrupt_mu_challenge, 4, |proof| {
        proof.mu = CF::random(&mut StdRng::seed_from_u64(780))
    });

    seeded_rejects!(rejects_corrupt_nu_challenge, 5, |proof| {
        proof.nu = CF::random(&mut StdRng::seed_from_u64(781))
    });

    seeded_rejects!(rejects_corrupt_mu_prime_challenge, 6, |proof| {
        proof.mu_prime = CF::random(&mut StdRng::seed_from_u64(782))
    });

    seeded_rejects!(rejects_corrupt_nu_prime_challenge, 7, |proof| {
        proof.nu_prime = CF::random(&mut StdRng::seed_from_u64(783))
    });

    seeded_rejects!(rejects_corrupt_x_challenge, 8, |proof| {
        proof.x = CF::random(&mut StdRng::seed_from_u64(784))
    });

    seeded_rejects!(rejects_corrupt_alpha_challenge, 9, |proof| {
        proof.alpha = CF::random(&mut StdRng::seed_from_u64(785))
    });

    seeded_rejects!(rejects_corrupt_u_challenge, 10, |proof| {
        proof.u = CF::random(&mut StdRng::seed_from_u64(786))
    });

    seeded_rejects!(rejects_corrupt_pre_beta_challenge, 11, |proof| {
        proof.pre_beta = CF::random(&mut StdRng::seed_from_u64(787))
    });

    seeded_rejects!(rejects_corrupt_preamble_bridge_commitment, 21, |proof| {
        proof.bridge_preamble_commitment = *Pasta::nested_generators(Pasta::baked()).h()
    });

    seeded_rejects!(rejects_corrupt_s_prime_bridge_commitment, 22, |proof| {
        proof.bridge_s_prime_commitment = *Pasta::nested_generators(Pasta::baked()).h()
    });

    seeded_rejects!(rejects_corrupt_inner_error_bridge_commitment, 23, |proof| {
        proof.bridge_inner_error_commitment = *Pasta::nested_generators(Pasta::baked()).h()
    });

    seeded_rejects!(rejects_corrupt_f_bridge_commitment, 27, |proof| {
        proof.bridge_f_commitment = *Pasta::nested_generators(Pasta::baked()).h()
    });

    seeded_rejects!(rejects_corrupt_preamble_native_rx, 29, |proof| {
        proof.native_preamble_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_inner_error_native_rx, 30, |proof| {
        proof.native_inner_error_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_outer_error_native_rx, 31, |proof| {
        proof.native_outer_error_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_query_native_rx, 32, |proof| {
        proof.native_query_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_eval_native_rx, 33, |proof| {
        proof.native_eval_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_application_rx, 34, |proof| {
        proof.native_application_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_hashes_1_rx, 35, |proof| {
        proof.native_hashes_1_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_hashes_2_rx, 36, |proof| {
        proof.native_hashes_2_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_inner_collapse_rx, 37, |proof| {
        proof.native_inner_collapse_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_outer_collapse_rx, 38, |proof| {
        proof.native_outer_collapse_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_compute_v_rx, 39, |proof| {
        proof.native_compute_v_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_registry_xy_poly, 40, |proof| {
        proof.native_registry_xy_poly = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_p_poly, 41, |proof| {
        proof.native_p_poly = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_nested_endoscalar_rx, 42, |proof| {
        proof.nested_endoscalar_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_nested_points_rx, 43, |proof| {
        proof.nested_points_rx = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    // NB-1: Early-return guard tests (circuit_id and header size)
    seeded_rejects!(rejects_corrupt_circuit_id, 50, |proof| {
        proof.circuit_id = CircuitIndex::new(9999)
    });

    seeded_rejects!(rejects_corrupt_left_header_length, 51, |proof| {
        proof.left_header.push(CF::ZERO)
    });

    seeded_rejects!(rejects_corrupt_right_header_length, 52, |proof| {
        proof.right_header.pop();
    });

    // NB-2: native_a_poly and native_b_poly feed the revdot claim
    seeded_rejects!(rejects_corrupt_native_a_poly, 53, |proof| {
        proof.native_a_poly = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    seeded_rejects!(rejects_corrupt_native_b_poly, 54, |proof| {
        proof.native_b_poly = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    // NB-3: Bridge rx polynomials (direct polynomial corruption)
    // These document verification gaps: the verifier does not yet independently
    // validate bridge rx polynomials. Un-ignore once verify() gains bridge
    // polynomial checks.
    #[test]
    #[ignore = "verification gap: bridge rx polynomials not independently checked"]
    fn rejects_corrupt_bridge_preamble_rx() {
        let (app, mut proof) = create_seeded_proof(55);
        proof.bridge_preamble_rx = ragu_circuits::polynomials::sparse::Polynomial::new();
        let mut rng = StdRng::seed_from_u64(99999);
        let pcd = proof.carry::<()>(());
        let result = app.verify(&pcd, &mut rng).expect("verify should not error");
        assert!(!result, "verifier must reject corrupt bridge_preamble_rx");
    }

    #[test]
    #[ignore = "verification gap: bridge rx polynomials not independently checked"]
    fn rejects_corrupt_bridge_s_prime_rx() {
        let (app, mut proof) = create_seeded_proof(56);
        proof.bridge_s_prime_rx = ragu_circuits::polynomials::sparse::Polynomial::new();
        let mut rng = StdRng::seed_from_u64(99999);
        let pcd = proof.carry::<()>(());
        let result = app.verify(&pcd, &mut rng).expect("verify should not error");
        assert!(!result, "verifier must reject corrupt bridge_s_prime_rx");
    }

    #[test]
    #[ignore = "verification gap: bridge rx polynomials not independently checked"]
    fn rejects_corrupt_bridge_inner_error_rx() {
        let (app, mut proof) = create_seeded_proof(57);
        proof.bridge_inner_error_rx = ragu_circuits::polynomials::sparse::Polynomial::new();
        let mut rng = StdRng::seed_from_u64(99999);
        let pcd = proof.carry::<()>(());
        let result = app.verify(&pcd, &mut rng).expect("verify should not error");
        assert!(
            !result,
            "verifier must reject corrupt bridge_inner_error_rx"
        );
    }

    #[test]
    #[ignore = "verification gap: bridge rx polynomials not independently checked"]
    fn rejects_corrupt_bridge_f_rx() {
        let (app, mut proof) = create_seeded_proof(58);
        proof.bridge_f_rx = ragu_circuits::polynomials::sparse::Polynomial::new();
        let mut rng = StdRng::seed_from_u64(99999);
        let pcd = proof.carry::<()>(());
        let result = app.verify(&pcd, &mut rng).expect("verify should not error");
        assert!(!result, "verifier must reject corrupt bridge_f_rx");
    }

    // NB-4: nested_endoscaling_step_rxs vector
    seeded_rejects!(rejects_corrupt_nested_endoscaling_step_rxs, 59, |proof| {
        proof.nested_endoscaling_step_rxs[0] = ragu_circuits::polynomials::sparse::Polynomial::new()
    });

    // NB-5: bridge_alpha scalar
    // Verification gap: bridge_alpha feeds cached bridge polynomials but the
    // verifier does not independently validate it. Un-ignore once verify()
    // gains a bridge_alpha check.
    #[test]
    #[ignore = "verification gap: bridge_alpha not independently checked"]
    fn rejects_corrupt_bridge_alpha() {
        let (app, mut proof) = create_seeded_proof(60);
        proof.bridge_alpha = <Pasta as Cycle>::ScalarField::random(&mut StdRng::seed_from_u64(800));
        let mut rng = StdRng::seed_from_u64(99999);
        let pcd = proof.carry::<()>(());
        let result = app.verify(&pcd, &mut rng).expect("verify should not error");
        assert!(!result, "verifier must reject corrupt bridge_alpha");
    }

    // NB-6: Corrupt commitment → challenge mismatch transcript replay
    #[test]
    fn verify_transcript_corrupt_commitment_shifts_challenges() {
        let pasta = Pasta::baked();
        let (_app, mut proof) = create_seeded_proof(7);

        // Corrupt a bridge commitment that is absorbed early in the transcript.
        proof.bridge_preamble_commitment = *Pasta::nested_generators(pasta).h();

        let dr = &mut ragu_core::drivers::emulator::Emulator::execute();
        let poseidon = Pasta::circuit_poseidon(pasta);
        let mut t = crate::internal::transcript::Transcript::new(dr, poseidon, crate::RAGU_TAG)
            .expect("transcript init should not fail");

        let preamble_commit =
            Point::<_, NestedCurve>::constant(dr, proof.bridge_preamble_commitment())
                .expect("point constant should not fail");
        preamble_commit
            .write(dr, &mut t)
            .expect("write should not fail");
        let w = *t
            .challenge(dr)
            .expect("challenge should not fail")
            .value()
            .take();

        // The corrupted commitment should produce a different w challenge.
        assert_ne!(
            w, proof.w,
            "corrupted preamble commitment must shift the w challenge"
        );
    }
}
