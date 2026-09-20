# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- Added sealed, static computational-backend selection between Ragu's reference
  and accelerated implementations, defaulting to
  `ragu_backend::ReferenceBackend`.
- Added `SelectableBackend::Verifier`, the backend whose kernels
  `Application::verify` consults, and support for
  `ragu_acceleration::AcceleratedProver`, which accelerates proving while
  verifying with the reference kernels.
- Added an opt-in `native-msm` feature for applications that select the
  accelerated backend.
- Added `RegistryTags`, the native and nested registry tags of an application,
  with `RegistryTags::from_beacon` to derive both from a public randomness
  beacon output and `RegistryTags::insecure_test_values` for tests.

### Changed

- `ApplicationBuilder::finalize` now takes the application's `RegistryTags`
  instead of deriving the registry tags from the registry polynomials. The
  registry tag (κ) must be sampled independently and without bias after the
  complete pre-keyed system description has been fixed and publicly
  committed, then permanently bound to that description; the description
  includes every registered step. See `ragu_circuits::registry::Tag`.
- Replaced the placeholder PCD transcript tag with `ragu-pcd-v1`. Proofs produced
  with the previous `FIXME` tag are incompatible with this protocol version.
- The `std` feature now enables the required `alloc` feature.
- Routed sparse polynomial evaluation, reverse-dot computations, registry
  evaluation, and polynomial commitments through the selected backend across
  proving and verification paths.
- `Application::verify` computes its acceptance kernels through the sealed
  `SelectableBackend::Verifier` of the selected backend rather than through
  the selected backend directly.

## [0.0.0] - 2025-11-05

### Added

- Initial commit.

[unreleased]: https://github.com/tachyon-zcash/ragu/compare/ragu_pcd-0.0.0...HEAD
[0.0.0]: https://github.com/tachyon-zcash/ragu/releases/tag/ragu_pcd-0.0.0
