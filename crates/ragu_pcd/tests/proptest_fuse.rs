//! Property-based tests for [`Application::fuse`] and multi-step PCD chains.
//!
//! The existing integration tests exercise fuse with fixed witness values
//! (`Fp::from(42)`). These proptests verify that seed, fuse, and rerandomize
//! work correctly for arbitrary field-element witnesses.

use proptest::prelude::*;
use proptest::test_runner::TestRunner;
use ragu_arithmetic::Cycle;
use ragu_circuits::polynomials::ProductionRank;
use ragu_pasta::{Fp, Pasta};
use ragu_pcd::{Application, ApplicationBuilder, Pcd};
use ragu_testing::{
    pcd::nontrivial::{Hash2, HashInternal2, InternalNode, LeafNode, WitnessLeaf},
    strategies::prime_field_element,
};
use rand::{SeedableRng, rngs::StdRng};

type App = Application<'static, Pasta, ProductionRank, 4>;
type Leaf = Pcd<Pasta, ProductionRank, LeafNode>;
type Node = Pcd<Pasta, ProductionRank, InternalNode>;

fn nontrivial_app() -> App {
    let pasta = Pasta::baked();
    let pp = Pasta::circuit_poseidon(pasta);
    ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(WitnessLeaf {
            poseidon_params: pp,
        })
        .unwrap()
        .register(Hash2 {
            poseidon_params: pp,
        })
        .unwrap()
        .register(HashInternal2 {
            poseidon_params: pp,
        })
        .unwrap()
        .finalize(pasta)
        .unwrap()
}

fn pp() -> &'static <Pasta as Cycle>::CircuitPoseidon {
    Pasta::circuit_poseidon(Pasta::baked())
}

fn fail(e: impl core::fmt::Display) -> TestCaseError {
    TestCaseError::fail(e.to_string())
}

fn runner(cases: u32) -> TestRunner {
    let mut config = ProptestConfig::with_cases(cases);
    config.failure_persistence = None;
    TestRunner::new(config)
}

fn seed(app: &App, rng: &mut StdRng, witness: Fp) -> Result<Leaf, TestCaseError> {
    app.seed(
        rng,
        WitnessLeaf {
            poseidon_params: pp(),
        },
        witness,
    )
    .map(|(leaf, _)| leaf)
    .map_err(fail)
}

fn fuse_leaves(
    app: &App,
    rng: &mut StdRng,
    left: Leaf,
    right: Leaf,
) -> Result<Node, TestCaseError> {
    app.fuse(
        rng,
        Hash2 {
            poseidon_params: pp(),
        },
        (),
        left,
        right,
    )
    .map(|(node, _)| node)
    .map_err(fail)
}

fn fuse_nodes(app: &App, rng: &mut StdRng, left: Node, right: Node) -> Result<Node, TestCaseError> {
    app.fuse(
        rng,
        HashInternal2 {
            poseidon_params: pp(),
        },
        (),
        left,
        right,
    )
    .map(|(node, _)| node)
    .map_err(fail)
}

/// Seeding with arbitrary field-element witnesses always produces a
/// verifiable leaf proof.
#[test]
fn seed_with_random_witness_verifies() {
    let app = nontrivial_app();
    let mut runner = runner(5);

    runner
        .run(&prime_field_element::<Fp>(), |witness| {
            let mut rng = StdRng::seed_from_u64(0xDEAD);
            let leaf = seed(&app, &mut rng, witness)?;
            let ok = app.verify(&leaf, &mut rng).map_err(fail)?;
            prop_assert!(ok, "leaf proof must verify");
            Ok(())
        })
        .unwrap();
}

/// Fusing two leaves seeded from independent random witnesses always
/// produces a verifiable proof.
#[test]
fn fuse_with_random_witnesses_verifies() {
    let app = nontrivial_app();
    let mut runner = runner(3);

    runner
        .run(
            &(prime_field_element::<Fp>(), prime_field_element::<Fp>()),
            |(w1, w2)| {
                let mut rng = StdRng::seed_from_u64(0xBEEF);
                let leaf1 = seed(&app, &mut rng, w1)?;
                let leaf2 = seed(&app, &mut rng, w2)?;
                let node = fuse_leaves(&app, &mut rng, leaf1, leaf2)?;

                let ok = app.verify(&node, &mut rng).map_err(fail)?;
                prop_assert!(ok, "fused proof must verify");
                Ok(())
            },
        )
        .unwrap();
}

/// Rerandomizing a fused proof preserves its header data and still verifies.
#[test]
fn fuse_then_rerandomize_preserves_data() {
    let app = nontrivial_app();
    let mut runner = runner(3);

    runner
        .run(
            &(prime_field_element::<Fp>(), prime_field_element::<Fp>()),
            |(w1, w2)| {
                let mut rng = StdRng::seed_from_u64(0xCAFE);
                let leaf1 = seed(&app, &mut rng, w1)?;
                let leaf2 = seed(&app, &mut rng, w2)?;
                let node = fuse_leaves(&app, &mut rng, leaf1, leaf2)?;

                let original_data = *node.data();
                let rerandomized = app.rerandomize(node, &mut rng).map_err(fail)?;

                prop_assert_eq!(
                    *rerandomized.data(),
                    original_data,
                    "rerandomization must preserve header data"
                );

                let ok = app.verify(&rerandomized, &mut rng).map_err(fail)?;
                prop_assert!(ok, "rerandomized fused proof must verify");
                Ok(())
            },
        )
        .unwrap();
}

/// A two-level fuse tree built from arbitrary leaf witnesses verifies.
#[test]
fn multi_step_fuse_chain_verifies() {
    let app = nontrivial_app();
    let mut runner = runner(2);
    let witnesses = (
        prime_field_element::<Fp>(),
        prime_field_element::<Fp>(),
        prime_field_element::<Fp>(),
        prime_field_element::<Fp>(),
    );

    runner
        .run(&witnesses, |(w1, w2, w3, w4)| {
            let mut rng = StdRng::seed_from_u64(0xF00D);
            let leaf1 = seed(&app, &mut rng, w1)?;
            let leaf2 = seed(&app, &mut rng, w2)?;
            let leaf3 = seed(&app, &mut rng, w3)?;
            let leaf4 = seed(&app, &mut rng, w4)?;

            let left = fuse_leaves(&app, &mut rng, leaf1, leaf2)?;
            let right = fuse_leaves(&app, &mut rng, leaf3, leaf4)?;
            let root = fuse_nodes(&app, &mut rng, left, right)?;

            let ok = app.verify(&root, &mut rng).map_err(fail)?;
            prop_assert!(ok, "multi-step fused proof must verify");
            Ok(())
        })
        .unwrap();
}
