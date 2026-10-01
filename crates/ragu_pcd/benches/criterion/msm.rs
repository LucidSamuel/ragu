//! Multiscalar multiplication over the baked host generators at Ragu's sizes.
//!
//! `Backend::msm` reaches Udon through `Affine::msm`, which plans serially
//! over bounded stack scratch. Udon's full path takes scratch sized from the
//! plan's requirements and a fork/join executor. The groups below measure the
//! difference, so the backend seam can decide what to expose.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use ragu_backend::{Backend, ReferenceBackend};
use ragu_core::{
    Cycle, FixedGenerators,
    pasta::{Eq, EqAffine, Fp, Pasta},
};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use udon::{
    curve::{AffineAdapter, AffinePoint, PastaCurve, ProjectivePoint, Vesta},
    exec::{ExecutionOptions, Executor, SerialExecutor, TaskBudget},
    field::{FieldAdapter, PastaField},
    msm::{Bases, Input, Requirements, ScalarStorage, Scratch},
};

/// Delegates to rayon's work-stealing join, as Udon's executor docs suggest.
struct RayonExecutor;

impl Executor for RayonExecutor {
    fn join<L, R, A, B>(&self, left: L, right: R) -> (A, B)
    where
        L: FnOnce() -> A + Send,
        R: FnOnce() -> B + Send,
        A: Send,
        B: Send,
    {
        rayon::join(left, right)
    }
}

/// Heap storage for one plan's requirements, reusable across executions.
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
            scalars: vec![ScalarStorage::ZERO; requirements.scalars()],
            digits: vec![0; requirements.digits()],
            affine: vec![AffinePoint::GENERATOR; requirements.affine()],
            projective: vec![ProjectivePoint::IDENTITY; requirements.projective()],
            field: vec![PastaField::ZERO; requirements.field()],
            indices: vec![0; requirements.indices()],
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

fn input<'a>(scalars: &'a [Fp], bases: &'a [EqAffine]) -> Input<'a, Vesta> {
    Input::new(
        Bases::Points(AffineAdapter::as_slice(bases)),
        FieldAdapter::as_slice(scalars),
    )
}

/// Udon's full path with scratch allocated for this call.
fn full_path<X: Executor>(
    scalars: &[Fp],
    bases: &[EqAffine],
    options: ExecutionOptions,
    executor: &X,
) -> ProjectivePoint<Vesta> {
    let input = input(scalars, bases);
    let mut scratch = HeapScratch::new(input.requirements(options).expect("plan"));
    input
        .execute(options, executor, scratch.borrow())
        .expect("sized scratch")
}

fn msm_bench(c: &mut Criterion) {
    let generators = Pasta::host_generators(ragu_pcd::pasta::baked()).g();
    let mut rng = StdRng::seed_from_u64(0x5a1a);
    let scalars: Vec<Fp> = (0..generators.len())
        .map(|_| Fp::from(rng.random::<u64>()))
        .collect();
    let threads = TaskBudget::new(rayon::current_num_threads()).expect("at least one thread");
    let parallel = ExecutionOptions::default().with_task_budget(threads);
    let serial = ExecutionOptions::default();

    let mut group = c.benchmark_group("msm");
    for log_size in [10u32, 12, 13] {
        let size = 1 << log_size;
        let (scalars, bases) = (&scalars[..size], &generators[..size]);

        // Every path must agree with the backend's current result.
        let expected: Eq = ReferenceBackend::msm(scalars.iter(), bases.iter());
        assert_eq!(
            full_path(scalars, bases, serial, &SerialExecutor),
            expected.into_inner()
        );
        assert_eq!(
            full_path(scalars, bases, parallel, &RayonExecutor),
            expected.into_inner()
        );

        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input(BenchmarkId::new("backend", size), &size, |b, _| {
            b.iter(|| ReferenceBackend::msm(black_box(scalars).iter(), black_box(bases).iter()))
        });
        group.bench_with_input(BenchmarkId::new("serial_heap", size), &size, |b, _| {
            b.iter(|| {
                full_path(
                    black_box(scalars),
                    black_box(bases),
                    serial,
                    &SerialExecutor,
                )
            })
        });
        group.bench_with_input(BenchmarkId::new("rayon_heap", size), &size, |b, _| {
            b.iter(|| {
                full_path(
                    black_box(scalars),
                    black_box(bases),
                    parallel,
                    &RayonExecutor,
                )
            })
        });
        // The scratch is sized and allocated once, then reborrowed per call.
        let input = input(scalars, bases);
        let mut scratch = HeapScratch::new(input.requirements(parallel).expect("plan"));
        group.bench_with_input(BenchmarkId::new("rayon_reused", size), &size, |b, _| {
            b.iter(|| {
                black_box(&input)
                    .execute(parallel, &RayonExecutor, scratch.borrow())
                    .expect("sized scratch")
            })
        });
    }
    group.finish();
}

criterion_group!(benches, msm_bench);
criterion_main!(benches);
