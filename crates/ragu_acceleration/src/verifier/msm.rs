//! Multiscalar multiplication over scratch sized for its input.
//!
//! The default [`Backend::msm`](ragu_backend::Backend::msm) reaches Udon
//! through [`Affine::msm`], which plans every input over about 14 KiB of
//! stack scratch and runs it serially. At Ragu's sizes that plan streams the
//! input through buckets far smaller than it. [`msm`] sizes heap scratch from
//! the plan's own requirements instead and, with the `multicore` feature,
//! runs the plan on rayon's pool.
//!
//! Udon's planner is specific to its Pasta curves, while `Backend::msm` is
//! generic over [`Affine`], which exposes no planner. The two Pasta adapters
//! are therefore recognized by type, and any other curve keeps the default
//! path.

use alloc::vec::Vec;
use core::any::Any;

#[cfg(not(feature = "multicore"))]
use udon::exec::SerialExecutor;
#[cfg(feature = "multicore")]
use udon::exec::TaskBudget;
use udon::{
    curve::{
        Affine, AffineAdapter, AffinePoint, Pallas, PastaCurve, ProjectiveAdapter, ProjectivePoint,
        Vesta,
    },
    exec::{ExecutionOptions, Executor},
    field::{FieldAdapter, PastaField},
    msm::{Bases, Input, Requirements, ScalarStorage, Scratch},
};

/// Computes $\langle \mathbf{a}, \mathbf{G} \rangle$ over the shorter of the
/// two inputs, matching [`Affine::msm`] on those paired elements.
pub(crate) fn msm<'a, C, A, B>(coeffs: A, bases: B) -> C::Projective
where
    C: Affine,
    A: IntoIterator<Item = &'a C::Scalar>,
    B: IntoIterator<Item = &'a C>,
{
    let mut coeffs: Vec<C::Scalar> = coeffs.into_iter().copied().collect();
    let mut bases: Vec<C> = bases.into_iter().copied().collect();
    let len = coeffs.len().min(bases.len());
    coeffs.truncate(len);
    bases.truncate(len);

    planned::<C, Pallas>(&coeffs, &bases)
        .or_else(|| planned::<C, Vesta>(&coeffs, &bases))
        .unwrap_or_else(|| C::msm(&coeffs, &bases))
}

/// The planned sum when `C` is Udon's adapter for `P`, and `None` otherwise.
fn planned<C: Affine, P: PastaCurve>(coeffs: &dyn Any, bases: &dyn Any) -> Option<C::Projective> {
    let scalars = coeffs.downcast_ref::<Vec<FieldAdapter<P::Scalar>>>()?;
    let points = bases.downcast_ref::<Vec<AffineAdapter<P>>>()?;
    let mut sum = Some(ProjectiveAdapter::new(execute(scalars, points)));
    (&mut sum as &mut dyn Any)
        .downcast_mut::<Option<C::Projective>>()?
        .take()
}

/// Plans the sum and runs it over scratch sized from the plan's requirements.
fn execute<P: PastaCurve>(
    scalars: &[FieldAdapter<P::Scalar>],
    points: &[AffineAdapter<P>],
) -> ProjectivePoint<P> {
    if points.is_empty() {
        return ProjectivePoint::IDENTITY;
    }
    let input = Input::new(
        Bases::Points(AffineAdapter::as_slice(points)),
        FieldAdapter::as_slice(scalars),
    );
    run(&input)
}

/// Runs `input` on rayon's pool, with one task per thread.
#[cfg(feature = "multicore")]
fn run<P: PastaCurve>(input: &Input<'_, P>) -> ProjectivePoint<P> {
    let threads = TaskBudget::new(maybe_rayon::current_num_threads()).expect("at least one thread");
    run_with(
        input,
        ExecutionOptions::default().with_task_budget(threads),
        &RayonExecutor,
    )
}

/// Runs `input` serially.
#[cfg(not(feature = "multicore"))]
fn run<P: PastaCurve>(input: &Input<'_, P>) -> ProjectivePoint<P> {
    run_with(input, ExecutionOptions::default(), &SerialExecutor)
}

fn run_with<P: PastaCurve, X: Executor>(
    input: &Input<'_, P>,
    options: ExecutionOptions,
    executor: &X,
) -> ProjectivePoint<P> {
    let requirements = input
        .requirements(options)
        .expect("a nonempty input plans without a workspace ceiling");
    let mut scratch = HeapScratch::new(requirements);
    input
        .execute(options, executor, scratch.borrow())
        .expect("scratch sized from the plan's requirements")
}

/// Delegates to rayon's work-stealing join, which meets [`Executor`]'s
/// progress requirement for nested joins.
#[cfg(feature = "multicore")]
struct RayonExecutor;

/// Heap storage for one plan's requirements.
struct HeapScratch<C: PastaCurve> {
    scalars: Vec<ScalarStorage<C>>,
    digits: Vec<u8>,
    affine: Vec<AffinePoint<C>>,
    projective: Vec<ProjectivePoint<C>>,
    field: Vec<PastaField<C::Base>>,
    indices: Vec<usize>,
}

impl<C: PastaCurve> HeapScratch<C> {
    fn new(requirements: Requirements) -> Self {
        Self {
            scalars: alloc::vec![ScalarStorage::ZERO; requirements.scalars()],
            digits: alloc::vec![0; requirements.digits()],
            affine: alloc::vec![AffinePoint::GENERATOR; requirements.affine()],
            projective: alloc::vec![ProjectivePoint::IDENTITY; requirements.projective()],
            field: alloc::vec![PastaField::ZERO; requirements.field()],
            indices: alloc::vec![0; requirements.indices()],
        }
    }

    fn borrow(&mut self) -> Scratch<'_, C> {
        Scratch::new(
            &mut self.scalars,
            &mut self.digits,
            &mut self.affine,
            &mut self.projective,
            &mut self.field,
            &mut self.indices,
        )
    }
}

#[cfg(feature = "multicore")]
impl Executor for RayonExecutor {
    fn join<L, R, A, B>(&self, left: L, right: R) -> (A, B)
    where
        L: FnOnce() -> A + Send,
        R: FnOnce() -> B + Send,
        A: Send,
        B: Send,
    {
        maybe_rayon::join(left, right)
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use proptest::prelude::*;
    use ragu_backend::{Backend, ReferenceBackend};
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use udon::{
        curve::{Affine, AffineAdapter, Pallas, Vesta},
        field::Field,
    };

    use super::planned;
    use crate::AcceleratedBackend;

    /// One past Ragu's production rank.
    const MAX_LEN: usize = 4097;

    /// Lengths at the planner's layout boundaries, up to the maximum, or
    /// anywhere below the first kernel switch.
    fn arb_len() -> impl Strategy<Value = usize> {
        prop_oneof![
            2 => prop::sample::select(
                &[0usize, 1, 2, 3, 15, 16, 17, 63, 64, 65, 255, 256, 257, 1024, 4096, MAX_LEN][..]
            ),
            1 => 0..=512usize,
        ]
    }

    /// Random scalars with zeros mixed in, over random points with identities
    /// mixed in.
    fn inputs<C: Affine>(seed: u64, len: usize) -> (Vec<C::Scalar>, Vec<C>) {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut random = || C::Scalar::random(|bytes| rng.fill_bytes(bytes));
        let scalars = (0..len)
            .map(|i| {
                if i % 7 == 3 {
                    C::Scalar::ZERO
                } else {
                    random()
                }
            })
            .collect();
        let points = (0..len)
            .map(|i| {
                if i % 11 == 5 {
                    C::identity()
                } else {
                    C::from(C::generator() * random())
                }
            })
            .collect();
        (scalars, points)
    }

    fn check_agrees_with_reference<C: Affine>(
        seed: u64,
        len: usize,
        truncate: usize,
    ) -> Result<(), TestCaseError> {
        let (scalars, points) = inputs::<C>(seed, len);
        prop_assert_eq!(
            AcceleratedBackend::msm(scalars.iter(), points.iter()),
            ReferenceBackend::msm(scalars.iter(), points.iter())
        );

        // Unequal lengths truncate to the shorter input, on either side.
        let truncate = truncate.min(len);
        prop_assert_eq!(
            AcceleratedBackend::msm(scalars[..truncate].iter(), points.iter()),
            ReferenceBackend::msm(scalars[..truncate].iter(), points.iter())
        );
        prop_assert_eq!(
            AcceleratedBackend::msm(scalars.iter(), points[..truncate].iter()),
            ReferenceBackend::msm(scalars.iter(), points[..truncate].iter())
        );
        Ok(())
    }

    proptest! {
        // The reference path is serial and unoptimized under test; each case
        // runs six of its sums.
        #![proptest_config(ProptestConfig::with_cases(32))]

        #[test]
        fn pallas_agrees_with_reference(
            seed in any::<u64>(),
            len in arb_len(),
            truncate in 0..=MAX_LEN,
        ) {
            check_agrees_with_reference::<AffineAdapter<Pallas>>(seed, len, truncate)?;
        }

        #[test]
        fn vesta_agrees_with_reference(
            seed in any::<u64>(),
            len in arb_len(),
            truncate in 0..=MAX_LEN,
        ) {
            check_agrees_with_reference::<AffineAdapter<Vesta>>(seed, len, truncate)?;
        }
    }

    #[test]
    fn pasta_adapters_take_the_planned_path() {
        let (scalars, points) = inputs::<AffineAdapter<Pallas>>(0x9e11, 8);
        assert!(planned::<AffineAdapter<Pallas>, Pallas>(&scalars, &points).is_some());
        assert!(planned::<AffineAdapter<Pallas>, Vesta>(&scalars, &points).is_none());

        let (scalars, points) = inputs::<AffineAdapter<Vesta>>(0x9e11, 8);
        assert!(planned::<AffineAdapter<Vesta>, Vesta>(&scalars, &points).is_some());
        assert!(planned::<AffineAdapter<Vesta>, Pallas>(&scalars, &points).is_none());
    }
}
