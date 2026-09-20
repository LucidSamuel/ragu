//! Application setup with caller-supplied registry tags.

use ragu_arithmetic::Cycle;
use ragu_circuits::{polynomials::Rank, registry::Tag};

use crate::{ApplicationBuilder, SelectableBackend};

/// The native and nested registry tags of an [`Application`](crate::Application).
///
/// API consumers must supply these through
/// [`ApplicationBuilder::with_registry_tags`]. Both values must be chosen
/// after the complete description, including every application step, was
/// fixed and publicly committed; see [`Tag::from_beacon`]. Production
/// consumers must not use a fixed test key.
pub struct RegistryTags<C: Cycle> {
    /// Tag for the native registry, over [`Cycle::CircuitField`].
    pub native: Tag<C::CircuitField>,
    /// Tag for the nested registry, over [`Cycle::ScalarField`].
    pub nested: Tag<C::ScalarField>,
}

impl<C: Cycle> RegistryTags<C> {
    /// Derives both tags from a public randomness beacon and the committed
    /// code hash, with distinct labels for the two registries. Both inputs
    /// are raw bytes, not hex strings. See [`Tag::from_beacon`].
    pub fn from_beacon(beacon: &[u8], code_hash: &[u8]) -> Self {
        Self {
            native: Tag::from_beacon(beacon, code_hash, b"ragu_pcd native registry"),
            nested: Tag::from_beacon(beacon, code_hash, b"ragu_pcd nested registry"),
        }
    }
}

impl<'params, C: Cycle, R: Rank, const HEADER_SIZE: usize, B: SelectableBackend>
    ApplicationBuilder<'params, C, R, HEADER_SIZE, B>
{
    /// Supplies the tags to use when [`Self::finalize`] builds both registries.
    ///
    /// The caller must choose the values after the complete application was
    /// fixed and publicly committed, following the ceremony described by
    /// [`Tag::from_beacon`]. This includes checking that the code hash
    /// identifies all registered circuits. No ceremony or code-hash checks
    /// are performed here. Production callers must not use a test key.
    pub fn with_registry_tags(mut self, tags: RegistryTags<C>) -> Self {
        self.native_registry = self.native_registry.with_tag(tags.native);
        self.nested_registry = self.nested_registry.with_tag(tags.nested);
        self
    }
}

#[cfg(test)]
mod tests {
    use ragu_circuits::polynomials::ProductionRank;
    use ragu_core::Result;
    use ragu_pasta::Pasta;

    use super::*;

    #[test]
    fn supplied_tags_reach_both_registries() -> Result<()> {
        let tags = RegistryTags::<Pasta>::from_beacon(&[0x42; 32], &[0x24; 20]);
        let native = tags.native.value();
        let nested = tags.nested.value();
        let app = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
            .with_registry_tags(tags)
            .finalize(Pasta::baked())?;
        assert_eq!(app.native_registry.tag(), native);
        assert_eq!(app.nested_registry.tag(), nested);
        Ok(())
    }
}
