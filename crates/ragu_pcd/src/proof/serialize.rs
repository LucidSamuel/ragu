//! `serde` support for [`CompressedProof`]: one byte string in the wire
//! format, so every serde data format carries the same bytes and the same
//! decoding checks apply.

use alloc::vec::Vec;
use core::{fmt, marker::PhantomData};

use ragu_arithmetic::Cycle;
use ragu_circuits::polynomials::Rank;
use ragu_primitives::wire::{Decode, Encode, Limits};
use serde::{
    Deserialize, Deserializer, Serialize, Serializer,
    de::{self, SeqAccess, Visitor},
};

use super::CompressedProof;

impl<C: Cycle, R: Rank> Serialize for CompressedProof<C, R>
where
    Self: Encode,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.to_bytes())
    }
}

/// Accepts the byte string however the format presents it: borrowed, owned,
/// or as a sequence in formats without a bytes type.
struct Bytes<C, R>(PhantomData<(C, R)>);

impl<'de, C: Cycle, R: Rank> Visitor<'de> for Bytes<C, R>
where
    CompressedProof<C, R>: Decode,
{
    type Value = CompressedProof<C, R>;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a compressed proof in its wire format")
    }

    fn visit_bytes<E: de::Error>(self, bytes: &[u8]) -> Result<Self::Value, E> {
        // The decoder borrows its error from the input, so it is rendered
        // before the input goes out of scope.
        CompressedProof::from_bytes(bytes, Limits::default()).map_err(E::custom)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut bytes = Vec::with_capacity(seq.size_hint().unwrap_or(0));
        while let Some(byte) = seq.next_element::<u8>()? {
            bytes.push(byte);
        }
        self.visit_bytes(&bytes)
    }
}

impl<'de, C: Cycle, R: Rank> Deserialize<'de> for CompressedProof<C, R>
where
    Self: Decode,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_bytes(Bytes(PhantomData))
    }
}
