use arithmetic::Cycle;
use ff::Field;
use ragu_circuits::{CircuitExt, polynomials::Rank};
use ragu_core::Result;
use rand::Rng;

use crate::{
    Application, Pcd, Proof, proof,
    step::{Step, internal::adapter::Adapter},
};

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    pub(super) fn compute_application_proof<'source, RNG: Rng, S: Step<C>>(
        &self,
        rng: &mut RNG,
        step: S,
        witness: S::Witness<'source>,
        left: Pcd<'source, C, R, S::Left>,
        right: Pcd<'source, C, R, S::Right>,
    ) -> Result<(
        Proof<C, R>,
        Proof<C, R>,
        proof::Application<C, R>,
        S::Aux<'source>,
    )> {
        let circuit_id = S::INDEX.circuit_index(self.num_application_steps)?;
        let (rx, aux) = Adapter::<C, S, R, HEADER_SIZE>::new(step).rx::<R>(
            (left.data, right.data, witness),
            self.circuit_mesh.get_key(),
        )?;
        let blind = C::CircuitField::random(&mut *rng);
        let commitment = rx.commit(C::host_generators(self.params), blind);

        let ((left_header, right_header), aux) = aux;

        Ok((
            left.proof,
            right.proof,
            proof::Application {
                circuit_id,
                left_header: left_header.into_inner(),
                right_header: right_header.into_inner(),
                rx,
                blind,
                commitment,
            },
            aux,
        ))
    }
}
