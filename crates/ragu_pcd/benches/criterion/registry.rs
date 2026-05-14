use criterion::{Criterion, black_box, criterion_group, criterion_main};
use ff::Field;
use ragu_arithmetic::Cycle;
use ragu_circuits::polynomials::ProductionRank;
use ragu_pasta::{Fp, Pasta};
use ragu_pcd::ApplicationBuilder;
use ragu_testing::pcd::nontrivial;
use rand::{SeedableRng, rngs::StdRng};

fn registry_bench(c: &mut Criterion) {
    let pasta = Pasta::baked();
    let poseidon_params = Pasta::circuit_poseidon(pasta);

    // Time finalize separately: build the ApplicationBuilder, then bench only finalize.
    let make_builder = || {
        ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
            .register(nontrivial::WitnessLeaf { poseidon_params })
            .unwrap()
            .register(nontrivial::Hash2 { poseidon_params })
            .unwrap()
    };

    c.bench_function("registry::finalize", |b| {
        b.iter_batched(
            make_builder,
            |builder| builder.finalize(pasta).unwrap(),
            criterion::BatchSize::PerIteration,
        );
    });

    // Build the finalized app once for evaluation benchmarks.
    let app = make_builder().finalize(pasta).unwrap();
    let registry = app.native_registry();

    // Use deterministic "random" field elements.
    let mut rng = StdRng::seed_from_u64(0xdead);
    let w = Fp::random(&mut rng);
    let x = Fp::random(&mut rng);
    let y = Fp::random(&mut rng);
    let x0 = Fp::random(&mut rng);
    let x1 = Fp::random(&mut rng);
    let u = Fp::random(&mut rng);

    c.bench_function("registry::wx", |b| {
        b.iter(|| registry.wx(w, x));
    });

    c.bench_function("registry::wy", |b| {
        b.iter(|| registry.wy(w, y));
    });

    c.bench_function("registry::wxy", |b| {
        b.iter(|| registry.wxy(w, x, y));
    });

    let registry_at_w = registry.at(w);
    c.bench_function("registry::wxy_separate3", |b| {
        b.iter(|| {
            black_box([
                registry_at_w.xy(x0, u),
                registry_at_w.xy(x1, u),
                registry_at_w.xy(u, y),
            ])
        });
    });

    let registry_wx0_poly = registry_at_w.x(x0);
    let registry_wx1_poly = registry_at_w.x(x1);
    let registry_wy_poly = registry_at_w.y(y);
    c.bench_function("registry::restriction_eval3", |b| {
        b.iter(|| {
            black_box([
                registry_wx0_poly.eval(u),
                registry_wx1_poly.eval(u),
                registry_wy_poly.eval(u),
            ])
        });
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = registry_bench
}
criterion_main!(benches);
