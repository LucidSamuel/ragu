use arithmetic::Cycle;
use ragu_circuits::{
    polynomials::{Rank, txz::Evaluate},
    staging::{StageBuilder, Staged, StagedCircuit},
};
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::GadgetKind,
    maybe::Maybe,
};
use ragu_primitives::{Element, GadgetExt, vec::Len};

use alloc::vec::Vec;
use core::marker::PhantomData;

use crate::components::fold_revdot::{NativeParameters, Parameters};

use super::{
    stages::native::{eval as native_eval, preamble as native_preamble, query as native_query},
    unified::{self, OutputBuilder},
};
use crate::components::horner::Horner;

pub use crate::internal_circuits::InternalCircuitIndex::ComputeVCircuit as CIRCUIT_ID;

pub struct Circuit<C: Cycle, R, const HEADER_SIZE: usize> {
    num_application_steps: usize,
    _marker: PhantomData<(C, R)>,
}

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Circuit<C, R, HEADER_SIZE> {
    pub fn new(num_application_steps: usize) -> Staged<C::CircuitField, R, Self> {
        Staged::new(Circuit {
            num_application_steps,
            _marker: PhantomData,
        })
    }
}

pub struct Witness<'a, C: Cycle, R: Rank, const HEADER_SIZE: usize> {
    pub unified_instance: &'a unified::Instance<C>,
    pub preamble_witness: &'a native_preamble::Witness<'a, C, R, HEADER_SIZE>,
    pub query_witness: &'a native_query::Witness<C>,
    pub eval_witness: &'a native_eval::Witness<'a, C, R>,
}

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> StagedCircuit<C::CircuitField, R>
    for Circuit<C, R, HEADER_SIZE>
{
    type Final = native_eval::Stage<C, R, HEADER_SIZE>;

    type Instance<'source> = &'source unified::Instance<C>;
    type Witness<'source> = Witness<'source, C, R, HEADER_SIZE>;
    type Output = unified::InternalOutputKind<C>;
    type Aux<'source> = ();

    fn instance<'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>>(
        &self,
        _: &mut D,
        _: DriverValue<D, Self::Instance<'source>>,
    ) -> Result<<Self::Output as GadgetKind<C::CircuitField>>::Rebind<'dr, D>>
    where
        Self: 'dr,
    {
        unreachable!("instance for internal circuits is not invoked")
    }

    fn witness<'a, 'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>>(
        &self,
        builder: StageBuilder<'a, 'dr, D, R, (), Self::Final>,
        witness: DriverValue<D, Self::Witness<'source>>,
    ) -> Result<(
        <Self::Output as GadgetKind<C::CircuitField>>::Rebind<'dr, D>,
        DriverValue<D, Self::Aux<'source>>,
    )>
    where
        Self: 'dr,
    {
        let (preamble, builder) =
            builder.add_stage::<native_preamble::Stage<C, R, HEADER_SIZE>>()?;
        let (query, builder) = builder.add_stage::<native_query::Stage<C, R, HEADER_SIZE>>()?;
        let (eval, builder) = builder.add_stage::<native_eval::Stage<C, R, HEADER_SIZE>>()?;
        let dr = builder.finish();

        let preamble = preamble.unenforced(dr, witness.view().map(|w| w.preamble_witness))?;

        // TODO: these are unenforced for now, because query/eval stages aren't
        // supposed to contain anything (yet) besides Elements, which require no
        // enforcement logic. Re-evaluate this in the future.
        let query = query.unenforced(dr, witness.view().map(|w| w.query_witness))?;
        let eval = eval.unenforced(dr, witness.view().map(|w| w.eval_witness))?;

        let unified_instance = &witness.view().map(|w| w.unified_instance);
        let mut unified_output = OutputBuilder::new();

        let w = unified_output.w.get(dr, unified_instance)?;
        let y = unified_output.y.get(dr, unified_instance)?;
        let z = unified_output.z.get(dr, unified_instance)?;
        let x = unified_output.x.get(dr, unified_instance)?;

        let txz = dr.routine(Evaluate::<R>::new(), (x.clone(), z.clone()))?;

        // Enforce the claimed value `v` in the unified instance is correctly
        // computed based on committed evaluation claims and verifier
        // challenges.
        {
            let (computed_ax, computed_bx) = {
                let mu = unified_output.mu.get(dr, unified_instance)?;
                let nu = unified_output.nu.get(dr, unified_instance)?;
                let mu_prime = unified_output.mu_prime.get(dr, unified_instance)?;
                let nu_prime = unified_output.nu_prime.get(dr, unified_instance)?;
                let mu_inv = mu.invert(dr)?;
                let mu_prime_inv = mu_prime.invert(dr)?;
                let munu = mu.mul(dr, &nu)?;
                let mu_prime_nu_prime = mu_prime.mul(dr, &nu_prime)?;

                compute_axbx::<_, NativeParameters>(
                    dr,
                    &query,
                    &z,
                    &txz,
                    &mu_inv,
                    &mu_prime_inv,
                    &munu,
                    &mu_prime_nu_prime,
                )?
            };

            // Compute expected f(u)
            let fu = {
                let alpha = unified_output.alpha.get(dr, unified_instance)?;
                let u = unified_output.u.get(dr, unified_instance)?;
                let denominators = Denominators::new(
                    dr,
                    &u,
                    &w,
                    &x,
                    &y,
                    &z,
                    &preamble,
                    self.num_application_steps,
                )?;
                let mut horner = Horner::new(dr, &alpha);
                for (pu, v, denominator) in poly_queries(
                    &eval,
                    &query,
                    &preamble,
                    &denominators,
                    &computed_ax,
                    &computed_bx,
                ) {
                    pu.sub(dr, v).mul(dr, denominator)?.write(dr, &mut horner)?;
                }
                horner.finish()
            };

            // Compute expected v = p(u)
            let computed_v = {
                let beta = unified_output.beta.get(dr, unified_instance)?;
                let mut horner = Horner::new(dr, &beta);
                fu.write(dr, &mut horner)?;
                eval.write(dr, &mut horner)?;
                horner.finish()
            };

            // When NOT in base case, enforce witnessed_v == computed_v.
            // In base case (both children trivial), prover may witness any v value.
            let witnessed_v = unified_output.v.get(dr, unified_instance)?;
            preamble
                .is_base_case(dr)?
                .not(dr)
                .conditional_enforce_equal(dr, &witnessed_v, &computed_v)?;
        }

        Ok((unified_output.finish(dr, unified_instance)?, D::just(|| ())))
    }
}

/// Denominator component of all quotient polynomial evaluations.
///
/// Each represents some $(u - x_i)^{-1}$.
struct Denominators<'dr, D: Driver<'dr>> {
    left_u: Element<'dr, D>,
    right_u: Element<'dr, D>,
    w: Element<'dr, D>,
    old_y0: Element<'dr, D>,
    old_y1: Element<'dr, D>,
    y: Element<'dr, D>,
    old_x0: Element<'dr, D>,
    old_x1: Element<'dr, D>,
    x: Element<'dr, D>,

    // Internal circuit omega^j denominators
    internal_preamble_stage: Element<'dr, D>,
    internal_error_m_stage: Element<'dr, D>,
    internal_error_n_stage: Element<'dr, D>,
    internal_query_stage: Element<'dr, D>,
    internal_eval_stage: Element<'dr, D>,
    internal_error_n_final_staged: Element<'dr, D>,
    internal_eval_final_staged: Element<'dr, D>,
    internal_hashes_1_circuit: Element<'dr, D>,
    internal_hashes_2_circuit: Element<'dr, D>,
    internal_partial_collapse_circuit: Element<'dr, D>,
    internal_full_collapse_circuit: Element<'dr, D>,
    internal_compute_v_circuit: Element<'dr, D>,

    // Child proof circuit_id denominators
    left_circuit_id: Element<'dr, D>,
    right_circuit_id: Element<'dr, D>,

    // xz denominator for circuit polynomial checks
    xz: Element<'dr, D>,
}

impl<'dr, D: Driver<'dr>> Denominators<'dr, D> {
    #[rustfmt::skip]
    fn new<C: Cycle, const HEADER_SIZE: usize>(
        dr: &mut D,
        u: &Element<'dr, D>,
        w: &Element<'dr, D>,
        x: &Element<'dr, D>,
        y: &Element<'dr, D>,
        z: &Element<'dr, D>,
        preamble: &native_preamble::Output<'dr, D, C, HEADER_SIZE>,
        num_application_steps: usize,
    ) -> Result<Self>
    where
        D::F: ff::PrimeField,
    {
        use super::InternalCircuitIndex::{self, *};

        let internal_denom = |dr: &mut D, idx: InternalCircuitIndex| -> Result<Element<'dr, D>> {
            let omega_j = Element::constant(dr, idx.circuit_index(num_application_steps).omega_j());
            u.sub(dr, &omega_j).invert(dr)
        };

        let xz = x.mul(dr, z)?;

        Ok(Denominators {
            left_u:  u.sub(dr, &preamble.left.unified.u).invert(dr)?,
            right_u: u.sub(dr, &preamble.right.unified.u).invert(dr)?,
            w:       u.sub(dr, w).invert(dr)?,
            old_y0:  u.sub(dr, &preamble.left.unified.y).invert(dr)?,
            old_y1:  u.sub(dr, &preamble.right.unified.y).invert(dr)?,
            y:       u.sub(dr, y).invert(dr)?,
            old_x0:  u.sub(dr, &preamble.left.unified.x).invert(dr)?,
            old_x1:  u.sub(dr, &preamble.right.unified.x).invert(dr)?,
            x:       u.sub(dr, x).invert(dr)?,
            internal_preamble_stage:           internal_denom(dr, PreambleStage)?,
            internal_error_m_stage:            internal_denom(dr, ErrorMStage)?,
            internal_error_n_stage:            internal_denom(dr, ErrorNStage)?,
            internal_query_stage:              internal_denom(dr, QueryStage)?,
            internal_eval_stage:               internal_denom(dr, EvalStage)?,
            internal_error_n_final_staged:     internal_denom(dr, ErrorNFinalStaged)?,
            internal_eval_final_staged:        internal_denom(dr, EvalFinalStaged)?,
            internal_hashes_1_circuit:         internal_denom(dr, Hashes1Circuit)?,
            internal_hashes_2_circuit:         internal_denom(dr, Hashes2Circuit)?,
            internal_partial_collapse_circuit: internal_denom(dr, PartialCollapseCircuit)?,
            internal_full_collapse_circuit:    internal_denom(dr, FullCollapseCircuit)?,
            internal_compute_v_circuit:        internal_denom(dr, ComputeVCircuit)?,
            left_circuit_id:  u.sub(dr, &preamble.left.circuit_id).invert(dr)?,
            right_circuit_id: u.sub(dr, &preamble.right.circuit_id).invert(dr)?,
            xz:              u.sub(dr, &xz).invert(dr)?,
        })
    }
}

fn fold_two_layer<'dr, D: Driver<'dr>, P: Parameters>(
    dr: &mut D,
    sources: &[Element<'dr, D>],
    layer1_scale: &Element<'dr, D>,
    layer2_scale: &Element<'dr, D>,
) -> Result<Element<'dr, D>> {
    let mut results = Vec::with_capacity(P::N::len());

    for chunk in sources.chunks(P::M::len()) {
        results.push(Element::fold(dr, chunk.iter(), layer1_scale)?);
    }

    while results.len() < P::N::len() {
        results.push(Element::zero(dr));
    }

    Element::fold(dr, results.iter(), layer2_scale)
}

struct SourceBuilder<'dr, D: Driver<'dr>> {
    z: Element<'dr, D>,
    txz: Element<'dr, D>,
    ax: Vec<Element<'dr, D>>,
    bx: Vec<Element<'dr, D>>,
}

impl<'dr, D: Driver<'dr>> SourceBuilder<'dr, D> {
    fn new(z: Element<'dr, D>, txz: Element<'dr, D>) -> Self {
        Self {
            z,
            txz,
            ax: Vec::new(),
            bx: Vec::new(),
        }
    }

    fn child(
        &mut self,
        dr: &mut D,
        fixed_mesh: &native_query::FixedMeshEvaluations<'dr, D>,
        child: &native_query::ChildEvaluations<'dr, D>,
    ) {
        self.direct(&child.a_poly_at_x, &child.b_poly_at_x);
        self.application(
            dr,
            &child.application_at_x,
            &child.application_at_xz,
            &child.new_mesh_xy_at_old_circuit_id,
        );
        self.internal(
            dr,
            [
                &child.hashes_1_at_x,
                &child.preamble_at_x,
                &child.error_n_at_x,
            ],
            [
                &child.hashes_1_at_xz,
                &child.preamble_at_xz,
                &child.error_n_at_xz,
            ],
            &fixed_mesh.hashes_1_circuit,
        );
        self.internal(
            dr,
            [&child.hashes_2_at_x, &child.error_n_at_x],
            [&child.hashes_2_at_xz, &child.error_n_at_xz],
            &fixed_mesh.hashes_2_circuit,
        );
        self.internal(
            dr,
            [
                &child.partial_collapse_at_x,
                &child.preamble_at_x,
                &child.error_m_at_x,
                &child.error_n_at_x,
            ],
            [
                &child.partial_collapse_at_xz,
                &child.preamble_at_xz,
                &child.error_m_at_xz,
                &child.error_n_at_xz,
            ],
            &fixed_mesh.partial_collapse_circuit,
        );
        self.internal(
            dr,
            [
                &child.full_collapse_at_x,
                &child.preamble_at_x,
                &child.error_m_at_x,
                &child.error_n_at_x,
            ],
            [
                &child.full_collapse_at_xz,
                &child.preamble_at_xz,
                &child.error_m_at_xz,
                &child.error_n_at_xz,
            ],
            &fixed_mesh.full_collapse_circuit,
        );
        self.internal(
            dr,
            [
                &child.compute_v_at_x,
                &child.preamble_at_x,
                &child.query_at_x,
                &child.eval_at_x,
            ],
            [
                &child.compute_v_at_xz,
                &child.preamble_at_xz,
                &child.query_at_xz,
                &child.eval_at_xz,
            ],
            &fixed_mesh.compute_v_circuit,
        );
    }

    fn direct(&mut self, ax_eval: &Element<'dr, D>, bx_eval: &Element<'dr, D>) {
        self.ax.push(ax_eval.clone());
        self.bx.push(bx_eval.clone());
    }

    fn application(
        &mut self,
        dr: &mut D,
        ax_eval: &Element<'dr, D>,
        bx_eval: &Element<'dr, D>,
        bx_mesh: &Element<'dr, D>,
    ) {
        self.ax.push(ax_eval.clone());
        self.bx.push(bx_eval.add(dr, bx_mesh).add(dr, &self.txz));
    }

    fn internal<'b>(
        &'b mut self,
        dr: &mut D,
        ax_evals: impl IntoIterator<Item = &'b Element<'dr, D>>,
        bx_evals: impl IntoIterator<Item = &'b Element<'dr, D>>,
        bx_mesh: &'b Element<'dr, D>,
    ) where
        'dr: 'b,
        D: 'b,
    {
        use core::iter;
        self.ax.push(Element::sum(dr, ax_evals));
        self.bx.push(Element::sum(
            dr,
            bx_evals
                .into_iter()
                .chain(iter::once(bx_mesh).chain(iter::once(&self.txz))),
        ));
    }

    fn stage<'b, I>(&mut self, dr: &mut D, ax_evals: I, bx_mesh: &Element<'dr, D>) -> Result<()>
    where
        'dr: 'b,
        D: 'b,
        I: IntoIterator<Item = &'b Element<'dr, D>>,
        I::IntoIter: DoubleEndedIterator,
    {
        self.ax
            .push(Element::fold(dr, ax_evals.into_iter(), &self.z)?);
        self.bx.push(bx_mesh.clone());
        Ok(())
    }

    fn build(self) -> (Vec<Element<'dr, D>>, Vec<Element<'dr, D>>) {
        (self.ax, self.bx)
    }
}

fn compute_axbx<'dr, D: Driver<'dr>, P: Parameters>(
    dr: &mut D,
    query: &native_query::Output<'dr, D>,
    z: &Element<'dr, D>,
    txz: &Element<'dr, D>,
    mu_inv: &Element<'dr, D>,
    mu_prime_inv: &Element<'dr, D>,
    munu: &Element<'dr, D>,
    mu_prime_nu_prime: &Element<'dr, D>,
) -> Result<(Element<'dr, D>, Element<'dr, D>)> {
    let mut builder = SourceBuilder::new(z.clone(), txz.clone());

    builder.child(dr, &query.fixed_mesh, &query.left);
    builder.child(dr, &query.fixed_mesh, &query.right);
    builder.stage(
        dr,
        [
            &query.left.hashes_1_at_x,
            &query.left.hashes_2_at_x,
            &query.left.partial_collapse_at_x,
            &query.left.full_collapse_at_x,
            &query.right.hashes_1_at_x,
            &query.right.hashes_2_at_x,
            &query.right.partial_collapse_at_x,
            &query.right.full_collapse_at_x,
        ],
        &query.fixed_mesh.error_n_final_staged,
    )?;
    builder.stage(
        dr,
        [&query.left.compute_v_at_x, &query.right.compute_v_at_x],
        &query.fixed_mesh.eval_final_staged,
    )?;
    builder.stage(
        dr,
        [&query.left.preamble_at_x, &query.right.preamble_at_x],
        &query.fixed_mesh.preamble_stage,
    )?;
    builder.stage(
        dr,
        [&query.left.error_m_at_x, &query.right.error_m_at_x],
        &query.fixed_mesh.error_m_stage,
    )?;
    builder.stage(
        dr,
        [&query.left.error_n_at_x, &query.right.error_n_at_x],
        &query.fixed_mesh.error_n_stage,
    )?;
    builder.stage(
        dr,
        [&query.left.query_at_x, &query.right.query_at_x],
        &query.fixed_mesh.query_stage,
    )?;
    builder.stage(
        dr,
        [&query.left.eval_at_x, &query.right.eval_at_x],
        &query.fixed_mesh.eval_stage,
    )?;

    let (ax_sources, bx_sources) = builder.build();
    let ax = fold_two_layer::<_, P>(dr, &ax_sources, mu_inv, mu_prime_inv)?;
    let bx = fold_two_layer::<_, P>(dr, &bx_sources, munu, mu_prime_nu_prime)?;
    Ok((ax, bx))
}

/// Returns an iterator over the queries.
///
/// Each yielded element represents $(p(u), v, (u - x_i)^{-1})$ where $v = p(x_i)$
/// is the prover's claim for that query.
#[rustfmt::skip]
fn poly_queries<'a, 'dr, D: Driver<'dr>, C: Cycle, const HEADER_SIZE: usize>(
    eval: &'a native_eval::Output<'dr, D>,
    query: &'a native_query::Output<'dr, D>,
    preamble: &'a native_preamble::Output<'dr, D, C, HEADER_SIZE>,
    d: &'a Denominators<'dr, D>,
    computed_ax: &'a Element<'dr, D>,
    computed_bx: &'a Element<'dr, D>,
) -> impl Iterator<Item = (&'a Element<'dr, D>, &'a Element<'dr, D>, &'a Element<'dr, D>)> {
    [
        // Check p(X) accumulator
        (&eval.left.p_poly,        &preamble.left.unified.v,          &d.left_u),
        (&eval.right.p_poly,       &preamble.right.unified.v,         &d.right_u),
        // Consistency checks for mesh polynomials
        (&eval.left.mesh_xy_poly,  &query.left.old_mesh_xy_at_new_w,  &d.w),
        (&eval.right.mesh_xy_poly, &query.right.old_mesh_xy_at_new_w, &d.w),
        (&eval.mesh_wx0,           &query.left.old_mesh_xy_at_new_w,  &d.old_y0),
        (&eval.mesh_wx1,           &query.right.old_mesh_xy_at_new_w, &d.old_y1),
        (&eval.mesh_wx0,           &query.left.new_mesh_wy_at_old_x,  &d.y),
        (&eval.mesh_wx1,           &query.right.new_mesh_wy_at_old_x, &d.y),
        (&eval.mesh_wy,            &query.left.new_mesh_wy_at_old_x,  &d.old_x0),
        (&eval.mesh_wy,            &query.right.new_mesh_wy_at_old_x, &d.old_x1),
        (&eval.mesh_wy,            &query.mesh_wxy,                   &d.x),
        (&eval.mesh_xy,            &query.mesh_wxy,                   &d.w),
        // Fixed mesh polynomial queries at internal circuit omega^j points
        (&eval.mesh_xy,            &query.fixed_mesh.preamble_stage,           &d.internal_preamble_stage),
        (&eval.mesh_xy,            &query.fixed_mesh.error_m_stage,            &d.internal_error_m_stage),
        (&eval.mesh_xy,            &query.fixed_mesh.error_n_stage,            &d.internal_error_n_stage),
        (&eval.mesh_xy,            &query.fixed_mesh.query_stage,              &d.internal_query_stage),
        (&eval.mesh_xy,            &query.fixed_mesh.eval_stage,               &d.internal_eval_stage),
        (&eval.mesh_xy,            &query.fixed_mesh.error_n_final_staged,     &d.internal_error_n_final_staged),
        (&eval.mesh_xy,            &query.fixed_mesh.eval_final_staged,        &d.internal_eval_final_staged),
        (&eval.mesh_xy,            &query.fixed_mesh.hashes_1_circuit,         &d.internal_hashes_1_circuit),
        (&eval.mesh_xy,            &query.fixed_mesh.hashes_2_circuit,         &d.internal_hashes_2_circuit),
        (&eval.mesh_xy,            &query.fixed_mesh.partial_collapse_circuit, &d.internal_partial_collapse_circuit),
        (&eval.mesh_xy,            &query.fixed_mesh.full_collapse_circuit,    &d.internal_full_collapse_circuit),
        (&eval.mesh_xy,            &query.fixed_mesh.compute_v_circuit,        &d.internal_compute_v_circuit),
        // Verify new_mesh_xy at child proof circuit_ids
        (&eval.mesh_xy,            &query.left.new_mesh_xy_at_old_circuit_id,  &d.left_circuit_id),
        (&eval.mesh_xy,            &query.right.new_mesh_xy_at_old_circuit_id, &d.right_circuit_id),
        // Child A/B polynomial queries at current x
        (&eval.left.a_poly,           &query.left.a_poly_at_x,           &d.x),
        (&eval.left.b_poly,           &query.left.b_poly_at_x,           &d.x),
        (&eval.right.a_poly,          &query.right.a_poly_at_x,          &d.x),
        (&eval.right.b_poly,          &query.right.b_poly_at_x,          &d.x),
        // Current step A/B polynomial queries at x
        (&eval.a_poly,                computed_ax,                 &d.x),
        (&eval.b_poly,                computed_bx,                 &d.x),
        // Left child proof stage/circuit polynomials
        (&eval.left.preamble,         &query.left.preamble_at_x,         &d.x),
        (&eval.left.preamble,         &query.left.preamble_at_xz,        &d.xz),
        (&eval.left.error_m,          &query.left.error_m_at_x,          &d.x),
        (&eval.left.error_m,          &query.left.error_m_at_xz,         &d.xz),
        (&eval.left.error_n,          &query.left.error_n_at_x,          &d.x),
        (&eval.left.error_n,          &query.left.error_n_at_xz,         &d.xz),
        (&eval.left.query,            &query.left.query_at_x,            &d.x),
        (&eval.left.query,            &query.left.query_at_xz,           &d.xz),
        (&eval.left.eval,             &query.left.eval_at_x,             &d.x),
        (&eval.left.eval,             &query.left.eval_at_xz,            &d.xz),
        (&eval.left.application,      &query.left.application_at_x,      &d.x),
        (&eval.left.application,      &query.left.application_at_xz,     &d.xz),
        (&eval.left.hashes_1,         &query.left.hashes_1_at_x,         &d.x),
        (&eval.left.hashes_1,         &query.left.hashes_1_at_xz,        &d.xz),
        (&eval.left.hashes_2,         &query.left.hashes_2_at_x,         &d.x),
        (&eval.left.hashes_2,         &query.left.hashes_2_at_xz,        &d.xz),
        (&eval.left.partial_collapse, &query.left.partial_collapse_at_x, &d.x),
        (&eval.left.partial_collapse, &query.left.partial_collapse_at_xz,&d.xz),
        (&eval.left.full_collapse,    &query.left.full_collapse_at_x,    &d.x),
        (&eval.left.full_collapse,    &query.left.full_collapse_at_xz,   &d.xz),
        (&eval.left.compute_v,        &query.left.compute_v_at_x,        &d.x),
        (&eval.left.compute_v,        &query.left.compute_v_at_xz,       &d.xz),
        // Right child proof stage/circuit polynomials
        (&eval.right.preamble,        &query.right.preamble_at_x,        &d.x),
        (&eval.right.preamble,        &query.right.preamble_at_xz,       &d.xz),
        (&eval.right.error_m,         &query.right.error_m_at_x,         &d.x),
        (&eval.right.error_m,         &query.right.error_m_at_xz,        &d.xz),
        (&eval.right.error_n,         &query.right.error_n_at_x,         &d.x),
        (&eval.right.error_n,         &query.right.error_n_at_xz,        &d.xz),
        (&eval.right.query,           &query.right.query_at_x,           &d.x),
        (&eval.right.query,           &query.right.query_at_xz,          &d.xz),
        (&eval.right.eval,            &query.right.eval_at_x,            &d.x),
        (&eval.right.eval,            &query.right.eval_at_xz,           &d.xz),
        (&eval.right.application,     &query.right.application_at_x,     &d.x),
        (&eval.right.application,     &query.right.application_at_xz,    &d.xz),
        (&eval.right.hashes_1,        &query.right.hashes_1_at_x,        &d.x),
        (&eval.right.hashes_1,        &query.right.hashes_1_at_xz,       &d.xz),
        (&eval.right.hashes_2,        &query.right.hashes_2_at_x,        &d.x),
        (&eval.right.hashes_2,        &query.right.hashes_2_at_xz,       &d.xz),
        (&eval.right.partial_collapse,&query.right.partial_collapse_at_x,&d.x),
        (&eval.right.partial_collapse,&query.right.partial_collapse_at_xz,&d.xz),
        (&eval.right.full_collapse,   &query.right.full_collapse_at_x,   &d.x),
        (&eval.right.full_collapse,   &query.right.full_collapse_at_xz,  &d.xz),
        (&eval.right.compute_v,       &query.right.compute_v_at_x,       &d.x),
        (&eval.right.compute_v,       &query.right.compute_v_at_xz,      &d.xz),
    ]
    .into_iter()
}
