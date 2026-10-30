//! Golden fixtures for the fuse pipeline and the compressed verifier.
//!
//! The fixtures under `tests/fixtures/fuse/` pin what [`Application::fuse`]
//! produces and what [`Application::verify_compressed`] accepts, so that a
//! change to either fails the `fuse fixtures` CI job instead of passing
//! silently. They follow the golden-proof harness of zakura-common's `sensei`
//! crate: the prover replays a committed randomness tape and must reproduce
//! the committed proof byte for byte, consuming exactly the tape.
//!
//! Each scenario is one proof in a fixed tree of fuses, with three files:
//!
//! - `<scenario>.rng-u64s-le`: the randomness the fuse drew, as little-endian
//!   `u64` words. Checking replays it and fails if the prover asks for more
//!   or leaves any unused, so the randomness schedule is pinned along with
//!   the output.
//! - `<scenario>.proof`: the header data and the compressed proof, in the
//!   test-local encoding below. The prover must reproduce these bytes, and
//!   the verifier must accept them as committed, without re-proving. The
//!   encoding is a fixture format, not a wire format. Compression draws a
//!   megabyte of blinding per proof, too much to commit as a tape, so its
//!   randomness comes from the frozen generator under a fixed seed and is
//!   pinned by its word count and by these bytes.
//! - `<scenario>.digests`: one BLAKE2b-256 digest per primary field of the
//!   uncompressed [`Proof`] the fuse produced, in declaration order, then the
//!   word counts the fuse and the compression drew and the `.proof` file's
//!   length. The uncompressed proof is over ten megabytes at production
//!   rank, so this stands in for committing it: a mismatch names the fields
//!   that drifted, and the file's diff in a pull request reads as the list
//!   of stages the change touched.
//!
//! After an intended change, regenerate with
//!
//! ```console
//! RAGU_FIXTURES=write cargo test --release -p ragu_pcd --all-features --lib proof::fuse_fixture_tests
//! ```
//!
//! and review the diff: it should name exactly the stages the change was
//! meant to touch.
//!
//! Every scenario runs once per profile, the wallet's [`Standard`] and the
//! [`Aggregator`], each with its own directory of fixtures. Both use the same
//! seeds, so a diff between the two directories is exactly what the profile
//! changes.
//!
//! [`Standard`]: crate::profile::Standard
//!
//! The steps are the fixtures' own: `ragu_testing`'s implement the `Step` of
//! the dev-dependency copy of this crate and cannot be registered from inside
//! it, and borrowing another suite's would let an edit there churn these
//! fixtures. Like sensei's harness, this one shares no code with the tests
//! around it.

use alloc::{
    format,
    string::{String, ToString},
    vec::Vec,
};
use core::{convert::Infallible, marker::PhantomData};
use std::{fs, path::PathBuf};

use blake2b_simd::{Params, State};
use ragu_backend::ReferenceBackend;
use ragu_circuits::{
    polynomials::{ProductionRank, Rank, sparse},
    registry::CircuitIndex,
};
use ragu_core::{
    Cycle, Result,
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Kind},
    maybe::Maybe,
    pasta::{Fp, Pasta, PastaParams},
};
use ragu_primitives::{
    Element,
    allocator::{Allocator, Standard},
    poseidon::Sponge,
};
use rand::{TryCryptoRng, TryRng};
use udon::{curve::Affine, field::Field};

use super::Proof;
use crate::{
    Application, ApplicationBuilder, CompressedProof, Pcd,
    compress::{
        Messages,
        batch::Batch,
        instance::{Child, Instance, NestedChild},
        revdot::{Reduction, fold::Fold},
    },
    header::{Header, Suffix},
    ipa::{IpaCycle, IpaProof},
    profile::{Aggregator, Profile, Profiled, ProfiledCycle},
    step::{Encoded, Index, Step, internal::bootstrap::Bootstrap},
};

type R = ProductionRank;
const HEADER_SIZE: usize = 4;
type App<C> = Application<'static, C, R, HEADER_SIZE>;
type TestPcd<C> = Pcd<C, R, Value>;

/// A profile of the Pasta cycle the fixtures prove in.
trait FixtureCycle: IpaCycle + ProfiledCycle + Cycle<CircuitField = Fp, Params = PastaParams> {
    /// The fixtures' application: their four steps at production rank, on
    /// the baked parameters.
    fn app() -> App<Self>;
}

impl<C> FixtureCycle for C
where
    C: IpaCycle + ProfiledCycle + Cycle<CircuitField = Fp, Params = PastaParams>,
    <C::Profile as Profile>::Context<'static, C::Base, R, ReferenceBackend>: Default,
{
    fn app() -> App<C> {
        ApplicationBuilder::<C, R, HEADER_SIZE>::new()
            .register(Seed::new())
            .and_then(|b| b.register(Merge::new()))
            .and_then(|b| b.register(UnitLeft::new()))
            .and_then(|b| b.register(UnitRight::new()))
            .and_then(|b| b.finalize(crate::pasta::baked()))
            .expect("the application must build")
    }
}

/// The fixtures' header: one field element.
struct Value;

impl Header<Fp> for Value {
    const SUFFIX: Suffix = Suffix::new(0);
    type Data = Fp;
    type Output = Kind![Fp; Element<'_, _>];

    fn encode<'dr, D: Driver<'dr, F = Fp>, A: Allocator<'dr, D>>(
        dr: &mut D,
        allocator: &mut A,
        witness: DriverValue<D, Fp>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        Element::alloc(dr, allocator, witness)
    }
}

/// Hashes both child headers and a salt into a [`Value`].
struct HashStep<L, H, const I: usize>(PhantomData<(L, H)>);

impl<L, H, const I: usize> HashStep<L, H, I> {
    fn new() -> Self {
        Self(PhantomData)
    }
}

impl<Cy, L: Header<Fp>, H: Header<Fp>, const I: usize> Step<Cy> for HashStep<L, H, I>
where
    Cy: Cycle<CircuitField = Fp, Params = PastaParams>,
{
    const INDEX: Index = Index::new(I);
    type Witness<'source> = Fp;
    type Aux<'source> = ();
    type Left = L;
    type Right = H;
    type Output = Value;

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = Fp>, const N: usize>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, Fp>,
        left: DriverValue<D, L::Data>,
        right: DriverValue<D, H::Data>,
    ) -> Result<(
        (
            Encoded<'dr, D, L, N>,
            Encoded<'dr, D, H, N>,
            Encoded<'dr, D, Value, N>,
        ),
        DriverValue<D, Fp>,
        DriverValue<D, ()>,
    )>
    where
        Self: 'dr,
    {
        let allocator = &mut Standard::new();
        let left = Encoded::new(dr, allocator, left)?;
        let right = Encoded::new(dr, allocator, right)?;
        let salt = Element::alloc(dr, allocator, witness)?;
        let mut sponge = Sponge::new(dr, Cy::circuit_poseidon(crate::pasta::baked()));
        let mut inputs = Vec::new();
        left.clone().write(dr, &mut inputs)?;
        right.clone().write(dr, &mut inputs)?;
        for input in inputs {
            sponge.absorb(dr, &input)?;
        }
        sponge.absorb(dr, &salt)?;
        let output = sponge.squeeze(dr)?;
        let data = output.value().map(|v| *v);
        Ok(((left, right, Encoded::from_gadget(output)), data, D::unit()))
    }
}

/// A seed: hashes two base-case children and a salt.
type Seed = HashStep<(), (), 0>;
/// Hashes two [`Value`] children and a salt.
type Merge = HashStep<Value, Value, 1>;
/// Hashes a base-case left child, a [`Value`] right child and a salt.
type UnitLeft = HashStep<(), Value, 2>;
/// Registered so the application has the support suite's shape; no
/// scenario fuses with it.
type UnitRight = HashStep<Value, (), 3>;

/// The command that rewrites the fixtures from the current prover.
const REGENERATE: &str = "RAGU_FIXTURES=write cargo test --release -p ragu_pcd --all-features --lib proof::fuse_fixture_tests";

/// The first bytes of every `.proof` file.
const MAGIC: &[u8; 8] = b"ragufx01";

/// The scenarios: a fixed tree of fuses over the fixtures' steps, each node
/// a fixture.
///
/// ```text
///                     rerandomize
///                          |
///                      merge_abcd
///                      /        \
///               merge_ab        merge_cd
///               /      \        /      \
///           seed_a  seed_b  seed_c  seed_d
///                  (each over the bootstrap proof)
/// ```
///
/// The `bootstrap` fixture is the base case every seed fuses as both
/// children; `unit_left` fuses it beside a seed as a `()`-header child.
const BOOTSTRAP: &str = "bootstrap";
const SEED_A: &str = "seed_a";
const SEED_B: &str = "seed_b";
const SEED_C: &str = "seed_c";
const SEED_D: &str = "seed_d";
const MERGE_AB: &str = "merge_ab";
const MERGE_CD: &str = "merge_cd";
const MERGE_ABCD: &str = "merge_abcd";
const UNIT_LEFT: &str = "unit_left";
const RERANDOMIZE: &str = "rerandomize";

/// The seed a scenario's tape is recorded from: a fixed prefix over a small
/// tag, so the seeds are recognizable and never collide. Checking replays
/// the recorded tape and does not use the seed.
const fn seed(tag: u64) -> u64 {
    0x5241_4755_4658_0000 | tag
}

/// A prover's randomness as a tape of `u64` words, in the manner of sensei's
/// `.rng-u64s-le` goldens.
///
/// Checking replays the committed tape and fails when the prover asks for a
/// word it does not hold; regenerating appends words from SplitMix64 as they
/// are drawn and writes the result. Either way `fill_bytes` takes whole
/// words, so a request's word count is fixed by its length, and the number
/// of words consumed pins the randomness schedule.
///
/// The generator is not cryptographically secure and must never produce a
/// real proof. It serves here only because the fixtures are synthetic test
/// data whose one requirement is a reproducible, platform-independent
/// stream that no dependency version can change: `StdRng` is pinned by
/// `Cargo.lock` but not by `rand`'s API. Changing it changes every tape
/// regenerated afterwards, not the committed ones.
struct Tape {
    words: Vec<u64>,
    cursor: usize,
    /// The generator state the next recorded word comes from, when
    /// recording.
    generator: Option<u64>,
}

impl Tape {
    fn replay(bytes: &[u8]) -> Self {
        assert!(
            bytes.len().is_multiple_of(8),
            "a tape is a whole number of little-endian u64 words"
        );
        Self {
            words: bytes
                .chunks_exact(8)
                .map(|word| u64::from_le_bytes(word.try_into().unwrap()))
                .collect(),
            cursor: 0,
            generator: None,
        }
    }

    fn record(seed: u64) -> Self {
        Self {
            words: Vec::new(),
            cursor: 0,
            generator: Some(seed),
        }
    }

    fn consumed(&self) -> usize {
        self.cursor
    }

    fn unused(&self) -> usize {
        self.words.len() - self.cursor
    }

    fn bytes(&self) -> Vec<u8> {
        self.words
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect()
    }

    fn word(&mut self) -> u64 {
        if self.cursor == self.words.len() {
            let state = self.generator.as_mut().unwrap_or_else(|| {
                panic!(
                    "the prover drew more randomness than the fixture's tape holds\nregenerate with\n    {REGENERATE}"
                )
            });
            *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut word = *state;
            word = (word ^ (word >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            word = (word ^ (word >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            self.words.push(word ^ (word >> 31));
        }
        let word = self.words[self.cursor];
        self.cursor += 1;
        word
    }
}

impl TryRng for Tape {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> core::result::Result<u32, Infallible> {
        Ok(self.word() as u32)
    }

    fn try_next_u64(&mut self) -> core::result::Result<u64, Infallible> {
        Ok(self.word())
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> core::result::Result<(), Infallible> {
        for chunk in dst.chunks_mut(8) {
            let word = self.word().to_le_bytes();
            chunk.copy_from_slice(&word[..chunk.len()]);
        }
        Ok(())
    }
}

impl TryCryptoRng for Tape {}

/// A BLAKE2b-256 digest of canonical bytes.
struct Digest(State);

impl Digest {
    fn new() -> Self {
        Self(Params::new().hash_length(32).to_state())
    }

    fn u64(&mut self, value: u64) {
        self.0.update(&value.to_le_bytes());
    }

    fn field<F: Field>(&mut self, value: &F) {
        self.0.update(value.to_bytes().as_ref());
    }

    fn point<P: Affine>(&mut self, value: &P) {
        self.0.update(value.to_bytes().as_ref());
    }

    fn fields<F: Field>(&mut self, values: &[F]) {
        self.u64(values.len() as u64);
        for value in values {
            self.field(value);
        }
    }

    /// Every coefficient in degree order, zeros included, so the digest is
    /// of the polynomial and not of its sparse storage.
    fn poly<F: Field, K: Rank>(&mut self, poly: &sparse::Polynomial<F, K>) {
        self.u64(K::num_coeffs() as u64);
        for coeff in poly.iter_coeffs() {
            self.field(&coeff);
        }
    }

    fn hex(self) -> String {
        self.0
            .finalize()
            .as_bytes()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }
}

fn digest(write: impl FnOnce(&mut Digest)) -> String {
    let mut digest = Digest::new();
    write(&mut digest);
    digest.hex()
}

/// The `key = value` lines of a `.digests` file, in order.
#[derive(Default)]
struct Lines(Vec<(String, String)>);

impl Lines {
    fn push(&mut self, key: impl Into<String>, value: impl ToString) {
        self.0.push((key.into(), value.to_string()));
    }

    fn field<F: Field>(&mut self, key: &str, value: &F) {
        self.push(key, digest(|d| d.field(value)));
    }

    fn fields<F: Field>(&mut self, key: &str, values: &[F]) {
        self.push(key, digest(|d| d.fields(values)));
    }

    fn point<P: Affine>(&mut self, key: &str, value: &P) {
        self.push(key, digest(|d| d.point(value)));
    }

    fn poly<F: Field, K: Rank>(&mut self, key: &str, poly: &sparse::Polynomial<F, K>) {
        self.push(key, digest(|d| d.poly(poly)));
    }

    fn polys<F: Field, K: Rank>(&mut self, key: &str, polys: &[sparse::Polynomial<F, K>]) {
        for (i, poly) in polys.iter().enumerate() {
            self.poly(&format!("{key}[{i}]"), poly);
        }
    }

    fn render(&self) -> String {
        let mut text = String::new();
        for (key, value) in &self.0 {
            text.push_str(key);
            text.push_str(" = ");
            text.push_str(value);
            text.push('\n');
        }
        text
    }

    fn parse(text: &str) -> Self {
        Self(
            text.lines()
                .filter(|line| !line.is_empty())
                .map(|line| {
                    let (key, value) = line
                        .split_once(" = ")
                        .expect("a fixture line is `key = value`");
                    (key.into(), value.into())
                })
                .collect(),
        )
    }
}

/// The digests of a proof's primary fields, in declaration order.
///
/// The destructuring is exhaustive: a field added to [`Proof`] does not
/// compile here until the fixture decides whether to pin it. The cached
/// commitments are derived from the polynomials they commit, and the bridge
/// `ab` polynomial from the commitments it carries, so they are not pinned
/// separately.
fn proof_lines<C: Cycle>(proof: &Proof<C, R>, lines: &mut Lines) {
    let Proof {
        bridge_alpha,
        circuit_id,
        left_header,
        right_header,
        native_application_rx,
        native_preamble_rx,
        native_inner_error_rx,
        native_outer_error_rx,
        native_a_poly,
        native_b_poly,
        native_query_rx,
        native_registry_xy_poly,
        native_eval_rx,
        native_p_poly,
        native_hashes_1_rx,
        native_hashes_2_rx,
        native_inner_collapse_rx,
        native_outer_collapse_rx,
        native_compute_v_rx,
        native_bind_challenges_rxs,
        native_bind_beta_rx,
        native_bind_endoscalar_rx,
        native_endoscaling_step_rxs,
        native_extension_circuit_rxs,
        native_extension_stage_rxs,
        native_points_binding_rx,
        native_points_children_rx,
        native_points_registry_wx_rx,
        native_points_ab_rx,
        native_points_f_rx,
        native_points_walk_rx,
        bridge_preamble_rx,
        bridge_s_prime_rx,
        bridge_inner_error_rx,
        bridge_outer_error_rx,
        bridge_query_rx,
        bridge_f_rx,
        bridge_eval_rx,
        bridge_ab_rx: _,
        nested_endoscaling_step_rxs,
        nested_extension_circuit_rxs,
        nested_extension_stage_rxs,
        nested_endoscalar_rx,
        nested_points_rx,
        nested_a_poly,
        nested_b_poly,
        nested_registry_xy_poly,
        nested_p_poly,
        nested_challenges_rx,
        nested_challenges_partial,
        nested_export_rx,
        nested_collapse_rx,
        nested_compute_v_rx,
        nested_endoscaling_step_commitments: _,
        nested_extension_circuit_commitments: _,
        nested_extension_stage_commitments: _,
        nested_endoscalar_commitment: _,
        nested_points_commitment: _,
        nested_a_commitment: _,
        nested_b_commitment: _,
        nested_registry_xy_commitment: _,
        nested_p_commitment: _,
        nested_challenges_commitment: _,
        nested_export_commitment: _,
        nested_collapse_commitment: _,
        nested_compute_v_commitment: _,
        w,
        y,
        z,
        mu,
        mu_prime,
        x,
        alpha,
        u,
        pre_beta,
        native_application_commitment: _,
        native_preamble_commitment: _,
        native_inner_error_commitment: _,
        native_outer_error_commitment: _,
        native_a_commitment: _,
        native_b_commitment: _,
        native_query_commitment: _,
        native_registry_xy_commitment: _,
        native_eval_commitment: _,
        native_p_commitment: _,
        native_hashes_1_commitment: _,
        native_hashes_2_commitment: _,
        native_inner_collapse_commitment: _,
        native_outer_collapse_commitment: _,
        native_compute_v_commitment: _,
        native_bind_challenges_commitments: _,
        native_bind_beta_commitment: _,
        native_bind_endoscalar_commitment: _,
        native_endoscaling_step_commitments: _,
        native_extension_circuit_commitments: _,
        native_extension_stage_commitments: _,
        native_points_binding_commitment: _,
        native_points_children_commitment: _,
        native_points_registry_wx_commitment: _,
        native_points_ab_commitment: _,
        native_points_f_commitment: _,
        native_points_walk_commitment: _,
        bridge_preamble_commitment: _,
        bridge_s_prime_commitment: _,
        bridge_inner_error_commitment: _,
        bridge_outer_error_commitment: _,
        bridge_query_commitment: _,
        bridge_f_commitment: _,
        bridge_eval_commitment: _,
        bridge_ab_commitment: _,
    } = proof;

    lines.push("circuit_id", usize::from(*circuit_id));
    lines.fields("left_header", left_header);
    lines.fields("right_header", right_header);
    lines.field("bridge_alpha", bridge_alpha);

    lines.poly("native_application_rx", native_application_rx);
    lines.poly("native_preamble_rx", native_preamble_rx);
    lines.poly("native_inner_error_rx", native_inner_error_rx);
    lines.poly("native_outer_error_rx", native_outer_error_rx);
    lines.poly("native_a_poly", native_a_poly);
    lines.poly("native_b_poly", native_b_poly);
    lines.poly("native_query_rx", native_query_rx);
    lines.poly("native_registry_xy_poly", native_registry_xy_poly);
    lines.poly("native_eval_rx", native_eval_rx);
    lines.poly("native_p_poly", native_p_poly);
    lines.poly("native_hashes_1_rx", native_hashes_1_rx);
    lines.poly("native_hashes_2_rx", native_hashes_2_rx);
    lines.poly("native_inner_collapse_rx", native_inner_collapse_rx);
    lines.poly("native_outer_collapse_rx", native_outer_collapse_rx);
    lines.poly("native_compute_v_rx", native_compute_v_rx);
    lines.polys("native_bind_challenges_rxs", native_bind_challenges_rxs);
    lines.poly("native_bind_beta_rx", native_bind_beta_rx);
    lines.poly("native_bind_endoscalar_rx", native_bind_endoscalar_rx);
    lines.polys("native_endoscaling_step_rxs", native_endoscaling_step_rxs);
    lines.polys("native_extension_circuit_rxs", native_extension_circuit_rxs);
    lines.polys("native_extension_stage_rxs", native_extension_stage_rxs);
    lines.poly("native_points_binding_rx", native_points_binding_rx);
    lines.poly("native_points_children_rx", native_points_children_rx);
    lines.poly("native_points_registry_wx_rx", native_points_registry_wx_rx);
    lines.poly("native_points_ab_rx", native_points_ab_rx);
    lines.poly("native_points_f_rx", native_points_f_rx);
    lines.poly("native_points_walk_rx", native_points_walk_rx);

    lines.poly("bridge_preamble_rx", bridge_preamble_rx);
    lines.poly("bridge_s_prime_rx", bridge_s_prime_rx);
    lines.poly("bridge_inner_error_rx", bridge_inner_error_rx);
    lines.poly("bridge_outer_error_rx", bridge_outer_error_rx);
    lines.poly("bridge_query_rx", bridge_query_rx);
    lines.poly("bridge_f_rx", bridge_f_rx);
    lines.poly("bridge_eval_rx", bridge_eval_rx);

    lines.polys("nested_endoscaling_step_rxs", nested_endoscaling_step_rxs);
    lines.polys("nested_extension_circuit_rxs", nested_extension_circuit_rxs);
    lines.polys("nested_extension_stage_rxs", nested_extension_stage_rxs);
    lines.poly("nested_endoscalar_rx", nested_endoscalar_rx);
    lines.poly("nested_points_rx", nested_points_rx);
    lines.poly("nested_a_poly", nested_a_poly);
    lines.poly("nested_b_poly", nested_b_poly);
    lines.poly("nested_registry_xy_poly", nested_registry_xy_poly);
    lines.poly("nested_p_poly", nested_p_poly);
    lines.poly("nested_challenges_rx", nested_challenges_rx);
    lines.point("nested_challenges_partial", nested_challenges_partial);
    lines.poly("nested_export_rx", nested_export_rx);
    lines.poly("nested_collapse_rx", nested_collapse_rx);
    lines.poly("nested_compute_v_rx", nested_compute_v_rx);

    lines.field("w", w);
    lines.field("y", y);
    lines.field("z", z);
    lines.field("mu", mu);
    lines.field("mu_prime", mu_prime);
    lines.field("x", x);
    lines.field("alpha", alpha);
    lines.field("u", u);
    lines.field("pre_beta", pre_beta);
}

/// Encoding of the header data a `.proof` file carries ahead of the proof.
trait FixtureHeader: Header<Fp> {
    fn write(data: &Self::Data, out: &mut Writer);
    fn read(cursor: &mut Cursor<'_>) -> Option<Self::Data>;
}

impl FixtureHeader for () {
    fn write(_: &(), _: &mut Writer) {}

    fn read(_: &mut Cursor<'_>) -> Option<()> {
        Some(())
    }
}

impl FixtureHeader for Value {
    fn write(data: &Fp, out: &mut Writer) {
        out.field(data);
    }

    fn read(cursor: &mut Cursor<'_>) -> Option<Fp> {
        cursor.field()
    }
}

/// Canonical fields and points, little-endian `u32` lengths.
#[derive(Default)]
struct Writer(Vec<u8>);

impl Writer {
    fn u32(&mut self, value: usize) {
        let value = u32::try_from(value).expect("fixture lengths fit in u32");
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    fn field<F: Field>(&mut self, value: &F) {
        self.0.extend_from_slice(value.to_bytes().as_ref());
    }

    fn point<P: Affine>(&mut self, value: &P) {
        self.0.extend_from_slice(value.to_bytes().as_ref());
    }

    fn fields<F: Field>(&mut self, values: &[F]) {
        self.u32(values.len());
        for value in values {
            self.field(value);
        }
    }

    fn points<P: Affine>(&mut self, values: &[P]) {
        self.u32(values.len());
        for value in values {
            self.point(value);
        }
    }
}

struct Cursor<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }

    fn take(&mut self, len: usize) -> Option<&'a [u8]> {
        let end = self.at.checked_add(len)?;
        let bytes = self.bytes.get(self.at..end)?;
        self.at = end;
        Some(bytes)
    }

    fn finished(&self) -> bool {
        self.at == self.bytes.len()
    }

    fn u32(&mut self) -> Option<usize> {
        let bytes = self.take(4)?;
        Some(u32::from_le_bytes(bytes.try_into().unwrap()) as usize)
    }

    fn field<F: Field>(&mut self) -> Option<F> {
        let mut repr = F::ZERO.to_bytes();
        let len = repr.as_ref().len();
        repr.as_mut().copy_from_slice(self.take(len)?);
        F::from_bytes(repr)
    }

    fn point<P: Affine>(&mut self) -> Option<P> {
        let mut repr = P::identity().to_bytes();
        let len = repr.as_ref().len();
        repr.as_mut().copy_from_slice(self.take(len)?);
        P::from_bytes(repr)
    }

    fn fields<F: Field>(&mut self) -> Option<Vec<F>> {
        let len = self.u32()?;
        (0..len).map(|_| self.field()).collect()
    }

    fn points<P: Affine>(&mut self) -> Option<Vec<P>> {
        let len = self.u32()?;
        (0..len).map(|_| self.point()).collect()
    }
}

/// Encodes a compressed proof, exhaustively over its fields, so that a field
/// added to the instance or the messages does not compile here until the
/// fixtures account for it.
fn encode_compressed<C: Cycle>(proof: &CompressedProof<C>, out: &mut Writer) {
    let CompressedProof {
        instance,
        native,
        nested,
    } = proof;
    out.0.extend_from_slice(MAGIC);

    let Instance {
        circuit_id,
        left_header,
        right_header,
        native: native_commitments,
        native_registry_xy,
        native_p,
        nested: nested_commitments,
        nested_registry_xy,
        nested_p,
        nested_challenges_partial,
        bridge_alpha,
        c,
        v,
        nested_c,
        nested_v,
        left,
        right,
        a_at_u,
        b_at_u,
        nested_left,
        nested_right,
        nested_a_at_u,
        nested_b_at_u,
    } = instance;
    out.u32(usize::from(*circuit_id));
    out.fields(left_header);
    out.fields(right_header);
    out.points(native_commitments);
    out.point(native_registry_xy);
    out.point(native_p);
    out.points(nested_commitments);
    out.point(nested_registry_xy);
    out.point(nested_p);
    out.point(nested_challenges_partial);
    out.field(bridge_alpha);
    out.field(c);
    out.field(v);
    out.field(nested_c);
    out.field(nested_v);
    for Child { x, y, id } in [left, right] {
        out.field(x);
        out.field(y);
        out.field(id);
    }
    out.field(a_at_u);
    out.field(b_at_u);
    for NestedChild { x, y } in [nested_left, nested_right] {
        out.field(x);
        out.field(y);
    }
    out.field(nested_a_at_u);
    out.field(nested_b_at_u);

    encode_messages(native, out);
    encode_messages(nested, out);
}

fn encode_messages<P: Affine>(messages: &Messages<P>, out: &mut Writer) {
    let Messages {
        reduction,
        batch,
        opening,
    } = messages;
    let Reduction {
        fold,
        p,
        q,
        openings,
        p_at_inverse_r,
        q_at_r,
    } = reduction;
    let Fold {
        inner,
        outer,
        inner_epsilon,
        outer_epsilon,
    } = fold;
    out.point(inner);
    out.point(outer);
    out.field(inner_epsilon);
    out.field(outer_epsilon);
    out.point(p);
    out.point(q);
    out.fields(openings);
    out.field(p_at_inverse_r);
    out.field(q_at_r);

    let Batch { f, evaluations } = batch;
    out.point(f);
    out.fields(evaluations);

    let IpaProof {
        s_commitment,
        rounds,
        c,
    } = opening;
    out.point(s_commitment);
    out.u32(rounds.len());
    for (left, right) in rounds {
        out.point(left);
        out.point(right);
    }
    out.field(c);
}

fn decode_compressed<C: Cycle>(cursor: &mut Cursor<'_>) -> Option<CompressedProof<C>> {
    if cursor.take(MAGIC.len())? != MAGIC {
        return None;
    }
    let circuit_id = CircuitIndex::new(cursor.u32()?);
    let left_header = cursor.fields()?;
    let right_header = cursor.fields()?;
    let native_commitments = cursor.points()?;
    let native_registry_xy = cursor.point()?;
    let native_p = cursor.point()?;
    let nested_commitments = cursor.points()?;
    let nested_registry_xy = cursor.point()?;
    let nested_p = cursor.point()?;
    let nested_challenges_partial = cursor.point()?;
    let bridge_alpha = cursor.field()?;
    let c = cursor.field()?;
    let v = cursor.field()?;
    let nested_c = cursor.field()?;
    let nested_v = cursor.field()?;
    let mut child = || {
        Some(Child {
            x: cursor.field()?,
            y: cursor.field()?,
            id: cursor.field()?,
        })
    };
    let left = child()?;
    let right = child()?;
    let a_at_u = cursor.field()?;
    let b_at_u = cursor.field()?;
    let mut nested_child = || {
        Some(NestedChild {
            x: cursor.field()?,
            y: cursor.field()?,
        })
    };
    let nested_left = nested_child()?;
    let nested_right = nested_child()?;
    let nested_a_at_u = cursor.field()?;
    let nested_b_at_u = cursor.field()?;
    let instance = Instance {
        circuit_id,
        left_header,
        right_header,
        native: native_commitments,
        native_registry_xy,
        native_p,
        nested: nested_commitments,
        nested_registry_xy,
        nested_p,
        nested_challenges_partial,
        bridge_alpha,
        c,
        v,
        nested_c,
        nested_v,
        left,
        right,
        a_at_u,
        b_at_u,
        nested_left,
        nested_right,
        nested_a_at_u,
        nested_b_at_u,
    };
    let native = decode_messages(cursor)?;
    let nested = decode_messages(cursor)?;
    Some(CompressedProof {
        instance,
        native,
        nested,
    })
}

fn decode_messages<P: Affine>(cursor: &mut Cursor<'_>) -> Option<Messages<P>> {
    let fold = Fold {
        inner: cursor.point()?,
        outer: cursor.point()?,
        inner_epsilon: cursor.field()?,
        outer_epsilon: cursor.field()?,
    };
    let reduction = Reduction {
        fold,
        p: cursor.point()?,
        q: cursor.point()?,
        openings: cursor.fields()?,
        p_at_inverse_r: cursor.field()?,
        q_at_r: cursor.field()?,
    };
    let batch = Batch {
        f: cursor.point()?,
        evaluations: cursor.fields()?,
    };
    let s_commitment = cursor.point()?;
    let rounds = (0..cursor.u32()?)
        .map(|_| Some((cursor.point()?, cursor.point()?)))
        .collect::<Option<Vec<_>>>()?;
    let opening = IpaProof {
        s_commitment,
        rounds,
        c: cursor.field()?,
    };
    Some(Messages {
        reduction,
        batch,
        opening,
    })
}

fn writing() -> bool {
    std::env::var_os("RAGU_FIXTURES").is_some_and(|mode| mode == "write")
}

/// One profile's fixtures: the directory they live in, and the label their
/// failures carry.
struct Fixtures {
    dir: PathBuf,
    profile: &'static str,
}

impl Fixtures {
    fn of<C: ProfiledCycle>() -> Self {
        let profile = <C::Profile as Profile>::NAME;
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/fuse")
            .join(profile);
        if writing() {
            fs::create_dir_all(&dir).expect("the fixture directory can be created");
        }
        Self { dir, profile }
    }

    fn label(&self, name: &str) -> String {
        format!("{}/{name}", self.profile)
    }

    fn path(&self, name: &str, extension: &str) -> PathBuf {
        self.dir.join(format!("{name}.{extension}"))
    }

    fn read(&self, name: &str, extension: &str) -> Vec<u8> {
        let path = self.path(name, extension);
        fs::read(&path).unwrap_or_else(|error| {
            panic!(
                "cannot read fixture {}: {error}\nregenerate with\n    {REGENERATE}",
                path.display()
            )
        })
    }

    fn write(&self, name: &str, extension: &str, bytes: &[u8]) {
        fs::write(self.path(name, extension), bytes).expect("the fixture directory is writable");
    }

    /// The tape a scenario replays, or a fresh one when regenerating.
    fn tape(&self, name: &str, tag: u64) -> Tape {
        if writing() {
            Tape::record(seed(tag))
        } else {
            Tape::replay(&self.read(name, "rng-u64s-le"))
        }
    }
}

/// The mismatches between the reproduced digests and the committed ones,
/// one line each.
fn compare_lines(label: &str, actual: &Lines, committed: &Lines) -> Vec<String> {
    let mut mismatches = Vec::new();
    for (key, value) in &actual.0 {
        match committed.0.iter().find(|(k, _)| k == key) {
            None => mismatches.push(format!("{label}: {key} is not in the fixture")),
            Some((_, expected)) if expected != value => {
                mismatches.push(format!("{label}: {key} changed"));
            }
            Some(_) => {}
        }
    }
    for (key, _) in &committed.0 {
        if !actual.0.iter().any(|(k, _)| k == key) {
            mismatches.push(format!("{label}: {key} is no longer produced"));
        }
    }
    mismatches
}

/// Checks one scenario after its fuse ran under `tape`: the tape is exactly
/// consumed, the uncompressed verifier accepts the proof, compressing it
/// under the fixed seed reproduces the committed `.proof` bytes, and the
/// digests match. When regenerating, writes the three files instead.
fn check<C: FixtureCycle, H: FixtureHeader>(
    app: &App<C>,
    fixtures: &Fixtures,
    name: &str,
    tag: u64,
    pcd: &Pcd<C, R, H>,
    tape: &Tape,
    failures: &mut Vec<String>,
) {
    let label = fixtures.label(name);
    let mut lines = Lines::default();
    proof_lines(pcd.proof(), &mut lines);

    // The verifier's randomness is not part of the fixture.
    let mut verifier = Tape::record(seed(0xff00));
    assert!(
        app.verify_uncompressed(pcd, &mut verifier)
            .expect("verification must not error"),
        "{label}: the uncompressed verifier rejected the reproduced proof"
    );

    let mut compress_rng = Tape::record(seed(0x100 | tag));
    let compressed = app
        .compress(pcd, &mut compress_rng)
        .expect("compression must succeed");

    let mut proof = Writer::default();
    H::write(pcd.data(), &mut proof);
    encode_compressed(compressed.proof(), &mut proof);

    lines.push("rng.fuse.words", tape.consumed());
    lines.push("rng.compress.words", compress_rng.consumed());
    lines.push("proof.bytes", proof.0.len());

    if writing() {
        fixtures.write(name, "rng-u64s-le", &tape.bytes());
        fixtures.write(name, "proof", &proof.0);
        fixtures.write(name, "digests", lines.render().as_bytes());
        return;
    }

    if tape.unused() != 0 {
        failures.push(format!(
            "{label}: the fuse left {} words of the tape unused",
            tape.unused()
        ));
    }
    if fixtures.read(name, "proof") != proof.0 {
        failures.push(format!("{label}: the compressed proof changed"));
    }
    let committed = Lines::parse(&String::from_utf8(fixtures.read(name, "digests")).unwrap());
    failures.extend(compare_lines(&label, &lines, &committed));
}

fn seed_scenario<C: FixtureCycle>(
    app: &App<C>,
    fixtures: &Fixtures,
    name: &str,
    tag: u64,
    salt: u64,
    failures: &mut Vec<String>,
) -> TestPcd<C> {
    let mut tape = fixtures.tape(name, tag);
    let (pcd, ()) = app
        .seed(&mut tape, Seed::new(), Fp::from(salt))
        .expect("seeding must succeed");
    check(app, fixtures, name, tag, &pcd, &tape, failures);
    pcd
}

#[allow(clippy::too_many_arguments)]
fn merge_scenario<C: FixtureCycle>(
    app: &App<C>,
    fixtures: &Fixtures,
    name: &str,
    tag: u64,
    salt: u64,
    left: TestPcd<C>,
    right: TestPcd<C>,
    failures: &mut Vec<String>,
) -> TestPcd<C> {
    let mut tape = fixtures.tape(name, tag);
    let (pcd, ()) = app
        .fuse(&mut tape, Merge::new(), Fp::from(salt), left, right)
        .expect("fusing two nodes must succeed");
    check(app, fixtures, name, tag, &pcd, &tape, failures);
    pcd
}

/// The prover reproduces every committed fixture of `C`'s profile.
///
/// The bootstrap proof `finalize` proves under `StdRng` is replaced by the
/// `bootstrap` scenario's, since every seed fuses it as both children and
/// the fixtures must move with fuse alone, not with `rand`'s generator.
fn prover_fixtures<C: FixtureCycle>() {
    let fixtures = Fixtures::of::<C>();
    let mut app = C::app();
    let mut failures = Vec::new();

    let mut bootstrap_tape = fixtures.tape(BOOTSTRAP, 1);
    let (bootstrap, ()) = app
        .fuse(
            &mut bootstrap_tape,
            Bootstrap::new(),
            (),
            app.dummy_pcd(),
            app.dummy_pcd(),
        )
        .expect("the bootstrap step must fuse");
    app.bootstrap = Some(bootstrap.proof().clone());
    check(
        &app,
        &fixtures,
        BOOTSTRAP,
        1,
        &bootstrap,
        &bootstrap_tape,
        &mut failures,
    );

    let seed_a = seed_scenario(&app, &fixtures, SEED_A, 2, 13, &mut failures);
    let seed_b = seed_scenario(&app, &fixtures, SEED_B, 3, 17, &mut failures);
    let seed_c = seed_scenario(&app, &fixtures, SEED_C, 4, 19, &mut failures);
    let seed_d = seed_scenario(&app, &fixtures, SEED_D, 5, 23, &mut failures);

    let mut unit_tape = fixtures.tape(UNIT_LEFT, 6);
    let (unit_left, ()) = app
        .fuse(
            &mut unit_tape,
            UnitLeft::new(),
            Fp::from(29u64),
            app.bootstrap_pcd(),
            seed_a.clone(),
        )
        .expect("fusing a unit child must succeed");
    check(
        &app,
        &fixtures,
        UNIT_LEFT,
        6,
        &unit_left,
        &unit_tape,
        &mut failures,
    );

    let merge_ab = merge_scenario(
        &app,
        &fixtures,
        MERGE_AB,
        7,
        31,
        seed_a,
        seed_b,
        &mut failures,
    );
    let merge_cd = merge_scenario(
        &app,
        &fixtures,
        MERGE_CD,
        8,
        37,
        seed_c,
        seed_d,
        &mut failures,
    );
    let merge_abcd = merge_scenario(
        &app,
        &fixtures,
        MERGE_ABCD,
        9,
        41,
        merge_ab,
        merge_cd,
        &mut failures,
    );

    // The first rerandomization also proves the seeded trivial proof the
    // step fuses against, so this tape covers both.
    let mut rerandomize_tape = fixtures.tape(RERANDOMIZE, 10);
    let rerandomized = app
        .rerandomize(merge_abcd, &mut rerandomize_tape)
        .expect("rerandomization must succeed");
    check(
        &app,
        &fixtures,
        RERANDOMIZE,
        10,
        &rerandomized,
        &rerandomize_tape,
        &mut failures,
    );

    assert!(
        failures.is_empty(),
        "the fuse fixtures changed:\n  {}\n\nIf the change is intended, regenerate them with\n    {REGENERATE}\nand review the diff.",
        failures.join("\n  ")
    );
}

/// Decodes a `.proof` file: header data, then the compressed proof, with
/// nothing after.
fn decode_fixture<C: Cycle, H: FixtureHeader>(
    bytes: &[u8],
) -> Option<(H::Data, CompressedProof<C>)> {
    let mut cursor = Cursor::new(bytes);
    let data = H::read(&mut cursor)?;
    let proof = decode_compressed::<C>(&mut cursor)?;
    cursor.finished().then_some((data, proof))
}

/// A committed `.proof` decodes and re-encodes to the same bytes, the
/// verifier accepts it without re-proving, and each tampered copy is
/// rejected.
fn verify_fixture<C: FixtureCycle, H: FixtureHeader>(
    app: &App<C>,
    fixtures: &Fixtures,
    name: &str,
    failures: &mut Vec<String>,
) {
    let label = fixtures.label(name);
    let bytes = fixtures.read(name, "proof");

    let Some((data, proof)) = decode_fixture::<C, H>(&bytes) else {
        failures.push(format!("{label}: the committed proof does not decode"));
        return;
    };
    let mut again = Writer::default();
    H::write(&data, &mut again);
    encode_compressed(&proof, &mut again);
    if again.0 != bytes {
        failures.push(format!("{label}: re-encoding changed the bytes"));
    }

    let verdict = app.verify_compressed(&proof.clone().carry::<H>(data.clone()));
    if !matches!(verdict, Ok(true)) {
        failures.push(format!(
            "{label}: the verifier rejected the committed compressed proof"
        ));
    }

    // Tampered copies: a wrong IPA scalar on either curve, and a wrong
    // claimed v.
    let mut rejected = |what: &str, proof: CompressedProof<C>| {
        let verdict = app.verify_compressed(&proof.carry::<H>(data.clone()));
        if !matches!(verdict, Ok(false)) {
            failures.push(format!("{label}: a proof with {what} was not rejected"));
        }
    };

    let mut tampered = proof.clone();
    tampered.native.opening.c += Fp::ONE;
    rejected("a wrong host IPA scalar", tampered);

    let mut tampered = proof.clone();
    tampered.nested.opening.c += C::ScalarField::ONE;
    rejected("a wrong nested IPA scalar", tampered);

    let mut tampered = proof;
    tampered.instance.v += Fp::ONE;
    rejected("a wrong claimed v", tampered);
}

/// The verifier accepts every committed compressed proof of `C`'s profile
/// and rejects tampered copies.
fn verifier_fixtures<C: FixtureCycle>() {
    if writing() {
        // The prover test is rewriting the files.
        return;
    }
    let fixtures = Fixtures::of::<C>();
    let app = C::app();
    let mut failures = Vec::new();
    verify_fixture::<C, ()>(&app, &fixtures, BOOTSTRAP, &mut failures);
    for name in [SEED_A, SEED_B, SEED_C, SEED_D, UNIT_LEFT] {
        verify_fixture::<C, Value>(&app, &fixtures, name, &mut failures);
    }
    for name in [MERGE_AB, MERGE_CD, MERGE_ABCD, RERANDOMIZE] {
        verify_fixture::<C, Value>(&app, &fixtures, name, &mut failures);
    }
    assert!(
        failures.is_empty(),
        "the verifier fixtures changed:\n  {}\n\nIf the change is intended, regenerate them with\n    {REGENERATE}\nand review the diff.",
        failures.join("\n  ")
    );
}

/// The wallet's profile.
mod standard {
    use super::*;

    #[cfg_attr(
        debug_assertions,
        ignore = "production-rank proving is impractically slow without --release"
    )]
    #[test]
    fn prover() {
        prover_fixtures::<Pasta>();
    }

    #[cfg_attr(
        debug_assertions,
        ignore = "production-rank proving is impractically slow without --release"
    )]
    #[test]
    fn verifier() {
        verifier_fixtures::<Pasta>();
    }
}

/// The aggregator's profile.
mod aggregator {
    use super::*;

    type C = Profiled<Pasta, Aggregator>;

    #[cfg_attr(
        debug_assertions,
        ignore = "production-rank proving is impractically slow without --release"
    )]
    #[test]
    fn prover() {
        prover_fixtures::<C>();
    }

    #[cfg_attr(
        debug_assertions,
        ignore = "production-rank proving is impractically slow without --release"
    )]
    #[test]
    fn verifier() {
        verifier_fixtures::<C>();
    }
}
