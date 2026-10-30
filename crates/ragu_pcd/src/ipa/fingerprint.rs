//! Test-only capture of a compressed verifier run, after zakura-common's
//! Halo2 verifier fingerprints.
//!
//! While [`capture`] runs, the cycle transcript records every point and
//! scalar it absorbs and every challenge it squeezes, and each IPA [`MSM`]
//! the verifier evaluates records its terms and whether it was the identity.
//! The fuse fixtures pin these, so a change to how the verifier reads a proof
//! shows even when its verdict does not.
//!
//! Recording is per thread and compiled only for tests: production builds
//! carry no hook.
//!
//! [`MSM`]: super::MSM

use alloc::vec::Vec;
use core::cell::RefCell;

use udon::{curve::Affine, field::Field};

/// One step of a verifier run.
pub(crate) enum Event {
    /// A point the transcript absorbed: a nested-curve point directly, or the
    /// bridge commitment of host-curve coordinates or nested-curve scalars.
    Point(Vec<u8>),
    /// A circuit-field scalar the transcript absorbed directly.
    Scalar(Vec<u8>),
    /// A challenge the transcript squeezed, in the circuit field.
    Challenge(Vec<u8>),
    /// An IPA MSM the verifier evaluated: its scalars in evaluation order,
    /// the proof-dependent bases they multiply, and whether it was the
    /// identity. The fixed generators are left out; their scalars' positions
    /// pin them.
    Msm {
        scalars: Vec<Vec<u8>>,
        bases: Vec<Vec<u8>>,
        identity: bool,
    },
}

std::thread_local! {
    static LOG: RefCell<Option<Vec<Event>>> = const { RefCell::new(None) };
}

/// Records an event if a capture is running on this thread.
pub(crate) fn record(event: impl FnOnce() -> Event) {
    LOG.with(|log| {
        if let Some(log) = log.borrow_mut().as_mut() {
            log.push(event());
        }
    });
}

/// Runs `run`, returning its output and the events it recorded.
pub(crate) fn capture<T>(run: impl FnOnce() -> T) -> (T, Vec<Event>) {
    LOG.with(|log| *log.borrow_mut() = Some(Vec::new()));
    let output = run();
    let events = LOG.with(|log| log.borrow_mut().take()).unwrap_or_default();
    (output, events)
}

pub(crate) fn field<F: Field>(value: &F) -> Vec<u8> {
    value.to_bytes().as_ref().to_vec()
}

pub(crate) fn point<P: Affine>(value: &P) -> Vec<u8> {
    value.to_bytes().as_ref().to_vec()
}
