//! Temporary replacement for evaluation-based registry tags.

use blake2b_simd::Params;
use ragu_arithmetic::ff::FromUniformBytes;
use ragu_core::Result;

use super::{RegistryBuilder, Tag};
use crate::polynomials::Rank;

impl<'params, F: FromUniformBytes<64>, R: Rank> RegistryBuilder<'params, F, R> {
    /// Supplies the registry tag to use at finalization.
    ///
    /// The API consumer must choose the value after the complete registry
    /// description was fixed and publicly committed. See [`Tag::from_beacon`]
    /// for the full ceremony requirement. This crate cannot check the
    /// ceremony or that the code hash identifies the registered circuits.
    pub fn with_tag(mut self, tag: Tag<F>) -> Self {
        self.tag = Some(tag);
        self
    }
}

pub(super) fn registry_tag<F: FromUniformBytes<64>>(tag: Option<Tag<F>>) -> Result<F> {
    if let Some(tag) = tag {
        return Ok(tag.value());
    }

    #[cfg(feature = "insecure-test-registry-tag")]
    {
        // Pin the test key independently of the production derivation:
        // witness regression fixtures depend on this digest.
        Ok(F::from_uniform_bytes(&[
            0xa7, 0x08, 0x75, 0xe4, 0xdd, 0x15, 0x68, 0x42, 0x4d, 0x83, 0xfa, 0x90, 0x81, 0x48,
            0x50, 0x0b, 0xa8, 0xf2, 0xe2, 0x74, 0x5d, 0x1a, 0xbf, 0xb5, 0x25, 0x15, 0xd4, 0x8f,
            0x5e, 0xb3, 0x30, 0xd0, 0x9f, 0x21, 0x70, 0xe5, 0x3e, 0x46, 0x24, 0x35, 0x6c, 0xa7,
            0x48, 0x4e, 0xf0, 0x53, 0x85, 0x1b, 0xe4, 0x87, 0x14, 0x0f, 0x68, 0xe9, 0x02, 0x13,
            0x5c, 0x76, 0xcb, 0x12, 0xd3, 0xa7, 0x4f, 0x02,
        ]))
    }

    #[cfg(not(feature = "insecure-test-registry-tag"))]
    {
        Err(ragu_core::Error::Initialization(
            "registry tag required: supply a value chosen after fixing the circuits with RegistryBuilder::with_tag".into(),
        ))
    }
}

impl<F: FromUniformBytes<64>> Tag<F> {
    /// Derives a registry tag from a public randomness beacon and a code hash.
    ///
    /// `beacon` is the raw beacon output, for example a block hash published
    /// after the registry's description was committed. `code_hash` is the raw
    /// digest identifying that description, for example a decoded commit hash
    /// covering all circuit code and the inputs that determine the registry.
    /// `label` separates the tags of distinct registries drawn from the same
    /// output, such as an application's native and nested registries.
    ///
    /// The label, code hash, and beacon output are absorbed in that order into
    /// BLAKE2b, personalized for this purpose. Each is prefixed by its byte
    /// length as a little-endian `u64`. The 64-byte digest is reduced to a
    /// uniform field element.
    ///
    /// # Ceremony requirement
    ///
    /// The complete untagged registry, including every application step, must
    /// be fixed and publicly committed before the beacon output is known.
    /// The beacon source, label, and derivation rule must also be fixed in
    /// advance; the circuit author must not control or grind the output.
    /// Changing the description requires a new ceremony.
    ///
    /// The caller must check that the code hash identifies the actual registry
    /// and that the commitment precedes the beacon. Mixing in an unchecked
    /// code hash does not establish either property. See the beacon proposal
    /// in [#78](https://github.com/tachyon-zcash/ragu/issues/78#issuecomment-3484495372).
    pub fn from_beacon(beacon: &[u8], code_hash: &[u8], label: &[u8]) -> Self {
        let digest = Params::new()
            .personal(b"ragu_tag_beacon_")
            .to_state()
            .update(&(label.len() as u64).to_le_bytes())
            .update(label)
            .update(&(code_hash.len() as u64).to_le_bytes())
            .update(code_hash)
            .update(&(beacon.len() as u64).to_le_bytes())
            .update(beacon)
            .finalize();
        Self(F::from_uniform_bytes(digest.as_array()))
    }
}

#[cfg(test)]
mod tests {
    use ragu_arithmetic::ff::Field;
    use ragu_core::Result;
    use ragu_pasta::{Fp, Fq, fp, fq};

    use super::*;
    use crate::{
        polynomials::{Rank, TestRank},
        registry::RegistryBuilder,
    };

    #[test]
    fn beacon_tags_match_vectors() {
        // Independently generated with Python hashlib.blake2b, then reduced
        // modulo Fp/Fq using the digest's little-endian integer value.
        assert_eq!(
            Tag::<Fp>::from_beacon(&[0x42; 32], &[0x24; 20], b"ragu_pcd native registry").value(),
            fp!(0x1c141fc950c9d298c205840012742d12b765e6cb495b9d4dccf775410d779870),
        );
        assert_eq!(
            Tag::<Fq>::from_beacon(&[0x42; 32], &[0x24; 20], b"ragu_pcd nested registry").value(),
            fq!(0x0d02d867670856cbd43265aff57b50accb9b3f7179e72859a43336609dd0ac6f),
        );
    }

    #[test]
    fn beacon_tag_binds_each_input() {
        let tag = Tag::<Fp>::from_beacon(b"beacon", b"code hash", b"label").value();
        for (beacon, code_hash, label) in [
            (&b"other beacon"[..], &b"code hash"[..], &b"label"[..]),
            (b"beacon", b"other code hash", b"label"),
            (b"beacon", b"code hash", b"other label"),
        ] {
            assert_ne!(
                tag,
                Tag::<Fp>::from_beacon(beacon, code_hash, label).value()
            );
        }
    }

    #[test]
    fn beacon_tag_separates_input_boundaries() {
        assert_ne!(
            Tag::<Fp>::from_beacon(b"bc", b"a", b"label").value(),
            Tag::<Fp>::from_beacon(b"c", b"ab", b"label").value(),
        );
        assert_ne!(
            Tag::<Fp>::from_beacon(b"beacon", b"bc", b"a").value(),
            Tag::<Fp>::from_beacon(b"beacon", b"c", b"ab").value(),
        );
    }

    #[test]
    fn beacon_tag_sets_the_registry_term() -> Result<()> {
        let tag = Tag::<Fp>::from_beacon(b"beacon", b"code hash", b"label");
        let value = tag.value();
        let mut registry = RegistryBuilder::<Fp, TestRank>::new()
            .with_tag(tag)
            .register_circuit(())?
            .finalize()?;
        assert_eq!(registry.tag(), value);

        let w = Fp::from(5);
        let x = Fp::from(2);
        let y = Fp::from(3);
        let tagged = registry.wxy(w, x, y);
        registry.tag = Tag::new(Fp::ZERO);
        assert_eq!(
            tagged - registry.wxy(w, x, y),
            value * (x * y).pow_vartime([(4 * TestRank::n() - 1) as u64]),
        );
        Ok(())
    }
}
