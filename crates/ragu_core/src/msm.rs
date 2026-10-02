//! Udon MSM execution with caller-owned scratch and Ragu's worker pool.

use alloc::{vec, vec::Vec};
use core::any::Any;

use udon::{
    curve::{
        Affine, AffineAdapter, AffinePoint, Pallas, PastaCurve, Point, ProjectiveAdapter,
        ProjectivePoint, Vesta,
    },
    exec::{ExecutionOptions, Executor, TaskBudget},
    field::{FieldAdapter, PastaField},
    msm::{Bases, Input, ScalarStorage, Scratch},
};

/// Computes $\sum_i \mathrm{scalars}_i \cdot \mathrm{bases}_i$.
///
/// Pasta MSMs use Udon's planner with scratch sized for the input and the
/// current Rayon pool when `multicore` is enabled. Other curves retain their
/// [`Affine::msm`] implementation. Empty inputs return the identity.
///
/// Inputs are collected into owned vectors; passing vectors reuses their
/// allocations. This lets the Pasta adapters borrow native buffers without
/// converting point or scalar encodings.
///
/// # Panics
///
/// Panics if the input lengths differ or the scratch size overflows.
pub fn msm<C: Affine>(
    scalars: impl IntoIterator<Item = C::Scalar>,
    bases: impl IntoIterator<Item = C>,
) -> C::Projective {
    let scalars: Vec<_> = scalars.into_iter().collect();
    let bases: Vec<_> = bases.into_iter().collect();
    assert_eq!(
        scalars.len(),
        bases.len(),
        "msm operands must have equal length"
    );

    if bases.is_empty() {
        return C::identity().to_projective();
    }

    // The generic curve trait has no executor or native-buffer interface.
    // Checked downcasts of the owned vectors select Pasta's safe borrowed
    // views without unsafe casts or per-element conversions.
    pasta::<C, Pallas>(&scalars, &bases)
        .or_else(|| pasta::<C, Vesta>(&scalars, &bases))
        .unwrap_or_else(|| C::msm(&scalars, &bases))
}

fn pasta<C: Affine, P: PastaCurve>(scalars: &dyn Any, bases: &dyn Any) -> Option<C::Projective> {
    let bases = bases.downcast_ref::<Vec<AffineAdapter<P>>>()?;
    let scalars = scalars
        .downcast_ref::<Vec<FieldAdapter<P::Scalar>>>()
        .expect("the selected Pasta curve's scalar type");
    let options = ExecutionOptions::default()
        .with_task_budget(TaskBudget::new(worker_count()).expect("at least one worker"));
    let result = ProjectiveAdapter::new(execute(
        FieldAdapter::as_slice(scalars),
        AffineAdapter::as_slice(bases),
        options,
        &PoolExecutor,
    ));
    Some(
        *(&result as &dyn Any)
            .downcast_ref::<C::Projective>()
            .expect("the selected Pasta curve's projective type"),
    )
}

fn execute<C: PastaCurve, X: Executor>(
    scalars: &[PastaField<C::Scalar>],
    bases: &[Point<C>],
    options: ExecutionOptions,
    executor: &X,
) -> ProjectivePoint<C> {
    let input = Input::new(Bases::Points(bases), scalars);
    let required = input.requirements(options).expect("MSM scratch size fits");
    let mut records = vec![ScalarStorage::ZERO; required.scalars()];
    let mut digits = vec![0; required.digits()];
    let mut affine = vec![AffinePoint::GENERATOR; required.affine()];
    let mut projective = vec![ProjectivePoint::IDENTITY; required.projective()];
    let mut field = vec![PastaField::ZERO; required.field()];
    let mut indices = vec![0; required.indices()];
    let scratch = Scratch::new(
        &mut records,
        &mut digits,
        &mut affine,
        &mut projective,
        &mut field,
        &mut indices,
    );
    input
        .execute(options, executor, scratch)
        .expect("scratch was sized for these inputs and execution options")
}

// Match maybe-rayon's serial fallback on WebAssembly without atomics.
#[cfg(all(
    feature = "multicore",
    not(all(target_arch = "wasm32", not(target_feature = "atomics")))
))]
fn worker_count() -> usize {
    maybe_rayon::current_num_threads()
}

#[cfg(not(all(
    feature = "multicore",
    not(all(target_arch = "wasm32", not(target_feature = "atomics")))
)))]
fn worker_count() -> usize {
    1
}

struct PoolExecutor;

impl Executor for PoolExecutor {
    fn join<L, R, A, B>(&self, left: L, right: R) -> (A, B)
    where
        L: FnOnce() -> A + Send,
        R: FnOnce() -> B + Send,
        A: Send,
        B: Send,
    {
        #[cfg(all(
            feature = "multicore",
            not(all(target_arch = "wasm32", not(target_feature = "atomics")))
        ))]
        {
            maybe_rayon::join(left, right)
        }
        #[cfg(not(all(
            feature = "multicore",
            not(all(target_arch = "wasm32", not(target_feature = "atomics")))
        )))]
        {
            // Also completes the right job if the left one panics, as the
            // Executor contract requires.
            udon::exec::SerialExecutor.join(left, right)
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    use rand::{Rng, SeedableRng, rngs::StdRng};
    use udon::{exec::SerialExecutor, field::Field};

    use super::*;

    struct CountingExecutor(AtomicUsize);

    impl Executor for CountingExecutor {
        fn join<L, R, A, B>(&self, left: L, right: R) -> (A, B)
        where
            L: FnOnce() -> A + Send,
            R: FnOnce() -> B + Send,
            A: Send,
            B: Send,
        {
            self.0.fetch_add(1, Ordering::Relaxed);
            SerialExecutor.join(left, right)
        }
    }

    fn planned_msm<C: PastaCurve>() {
        let mut rng = StdRng::seed_from_u64(462);
        let scalars: Vec<_> = (0..2049)
            .map(|_| FieldAdapter::<C::Scalar>::random(|bytes| rng.fill_bytes(bytes)))
            .collect();
        let generator = AffineAdapter::<C>::generator();
        let bases: Vec<_> = (0..scalars.len())
            .map(|i| match i % 3 {
                0 => generator,
                1 => -generator,
                _ => AffineAdapter::identity(),
            })
            .collect();
        let expected = AffineAdapter::<C>::msm(&scalars, &bases);
        let options = ExecutionOptions::default().with_task_budget(TaskBudget::new(4).unwrap());
        let executor = CountingExecutor(AtomicUsize::new(0));
        let actual = ProjectiveAdapter::new(execute(
            FieldAdapter::as_slice(&scalars),
            AffineAdapter::as_slice(&bases),
            options,
            &executor,
        ));
        assert_eq!(actual, expected);
        assert!(
            executor.0.load(Ordering::Relaxed) > 0,
            "Udon must use the supplied executor"
        );

        // Exercise the generic adapter's checked dispatch as well.
        assert_eq!(msm(scalars, bases), expected);
    }

    #[test]
    fn pallas_plan_uses_executor() {
        planned_msm::<Pallas>();
    }

    #[test]
    fn vesta_plan_uses_executor() {
        planned_msm::<Vesta>();
    }

    #[test]
    fn executor_completes_right_job_after_left_panic() {
        let completed = AtomicBool::new(false);
        let result = std::panic::catch_unwind(|| {
            PoolExecutor.join(
                || panic!("left job"),
                || completed.store(true, Ordering::Relaxed),
            )
        });
        assert!(result.is_err());
        assert!(completed.load(Ordering::Relaxed));
    }
}
