//! Property-based tests for [`Application::fuse`] and multi-step PCD chains.
//!
//! The existing integration tests exercise fuse with fixed witness values
//! (`Fp::from(42)`). These proptests verify that seed, fuse, and rerandomize
//! work correctly for arbitrary field-element witnesses and RNG seeds.

use proptest::{prelude::*, test_runner::TestRunner};
use ragu_arithmetic::Cycle;
use ragu_circuits::polynomials::ProductionRank;
use ragu_core::{drivers::emulator::Emulator, maybe::Maybe};
use ragu_pasta::{Fp, Pasta};
use ragu_pcd::{Application, ApplicationBuilder, Pcd};
use ragu_primitives::{Element, allocator::Standard, poseidon::Sponge};
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

fn hash_leaf(witness: Fp) -> Result<Fp, TestCaseError> {
    Emulator::emulate_wireless(witness, |dr, witness| {
        let witness = Element::alloc(dr, &mut Standard::new(), witness)?;
        let mut sponge = Sponge::new(dr, pp());
        sponge.absorb(dr, &witness)?;
        Ok(*sponge.squeeze(dr)?.value().take())
    })
    .map_err(fail)
}

fn hash_pair(left: Fp, right: Fp) -> Result<Fp, TestCaseError> {
    Emulator::emulate_wireless((left, right), |dr, witness| {
        let (left, right) = witness.cast();
        let left = Element::alloc(dr, &mut Standard::new(), left)?;
        let right = Element::alloc(dr, &mut Standard::new(), right)?;
        let mut sponge = Sponge::new(dr, pp());
        sponge.absorb(dr, &left)?;
        sponge.absorb(dr, &right)?;
        Ok(*sponge.squeeze(dr)?.value().take())
    })
    .map_err(fail)
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
        .run(
            &(prime_field_element::<Fp>(), any::<u64>()),
            |(witness, rng_seed)| {
                let mut rng = StdRng::seed_from_u64(rng_seed);
                let leaf = seed(&app, &mut rng, witness)?;
                prop_assert_eq!(
                    *leaf.data(),
                    hash_leaf(witness)?,
                    "leaf data must equal the Poseidon hash of its witness"
                );
                let ok = app.verify(&leaf, &mut rng).map_err(fail)?;
                prop_assert!(ok, "leaf proof must verify");
                Ok(())
            },
        )
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
            &(
                prime_field_element::<Fp>(),
                prime_field_element::<Fp>(),
                any::<u64>(),
            ),
            |(w1, w2, rng_seed)| {
                let mut rng = StdRng::seed_from_u64(rng_seed);
                let leaf1 = seed(&app, &mut rng, w1)?;
                let leaf2 = seed(&app, &mut rng, w2)?;
                let expected_leaf1 = hash_leaf(w1)?;
                let expected_leaf2 = hash_leaf(w2)?;
                prop_assert_eq!(*leaf1.data(), expected_leaf1);
                prop_assert_eq!(*leaf2.data(), expected_leaf2);

                let node = fuse_leaves(&app, &mut rng, leaf1, leaf2)?;
                prop_assert_eq!(
                    *node.data(),
                    hash_pair(expected_leaf1, expected_leaf2)?,
                    "fused node data must hash its child data"
                );

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
            &(
                prime_field_element::<Fp>(),
                prime_field_element::<Fp>(),
                any::<u64>(),
            ),
            |(w1, w2, rng_seed)| {
                let mut rng = StdRng::seed_from_u64(rng_seed);
                let leaf1 = seed(&app, &mut rng, w1)?;
                let leaf2 = seed(&app, &mut rng, w2)?;
                let expected_data = hash_pair(hash_leaf(w1)?, hash_leaf(w2)?)?;
                let node = fuse_leaves(&app, &mut rng, leaf1, leaf2)?;
                prop_assert_eq!(
                    *node.data(),
                    expected_data,
                    "fused node data must hash its child data"
                );

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
        any::<u64>(),
    );

    runner
        .run(&witnesses, |(w1, w2, w3, w4, rng_seed)| {
            let mut rng = StdRng::seed_from_u64(rng_seed);
            let leaf1 = seed(&app, &mut rng, w1)?;
            let leaf2 = seed(&app, &mut rng, w2)?;
            let leaf3 = seed(&app, &mut rng, w3)?;
            let leaf4 = seed(&app, &mut rng, w4)?;

            let expected_leaf1 = hash_leaf(w1)?;
            let expected_leaf2 = hash_leaf(w2)?;
            let expected_leaf3 = hash_leaf(w3)?;
            let expected_leaf4 = hash_leaf(w4)?;
            prop_assert_eq!(*leaf1.data(), expected_leaf1);
            prop_assert_eq!(*leaf2.data(), expected_leaf2);
            prop_assert_eq!(*leaf3.data(), expected_leaf3);
            prop_assert_eq!(*leaf4.data(), expected_leaf4);

            let left = fuse_leaves(&app, &mut rng, leaf1, leaf2)?;
            let right = fuse_leaves(&app, &mut rng, leaf3, leaf4)?;
            let expected_left = hash_pair(expected_leaf1, expected_leaf2)?;
            let expected_right = hash_pair(expected_leaf3, expected_leaf4)?;
            prop_assert_eq!(*left.data(), expected_left);
            prop_assert_eq!(*right.data(), expected_right);

            let root = fuse_nodes(&app, &mut rng, left, right)?;
            prop_assert_eq!(
                *root.data(),
                hash_pair(expected_left, expected_right)?,
                "root data must equal the nested Poseidon hash"
            );

            let ok = app.verify(&root, &mut rng).map_err(fail)?;
            prop_assert!(ok, "multi-step fused proof must verify");
            Ok(())
        })
        .unwrap();
}
