# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- Added iteration over the stored coefficients of sparse polynomials.
- Added `Tag::from_beacon`, which derives a registry tag from a public
  randomness beacon output, and `Tag::insecure_test_value` for tests.
- Added `Registry::evaluation_digest` under the `test-utils` feature: a
  non-binding regression digest of the registry polynomial.

### Changed

- Renamed `registry::Key` to `registry::Tag` and `Registry::digest()` to
  `Registry::tag()`.
- `RegistryBuilder::finalize` now takes the registry `Tag` instead of deriving
  it from the registry polynomial. The registry tag (κ) must be sampled
  independently and without bias after the complete pre-keyed system
  description has been fixed and publicly committed, then permanently bound
  to that description; see the `Tag` documentation.

### Removed

- Removed the derivation of the registry tag from evaluations of the registry
  polynomial, which did not bind the polynomial. Its hash now serves only as
  `Registry::evaluation_digest`.

## [0.0.0] - 2025-07-29

### Added

- Initial commit.

[unreleased]: https://github.com/tachyon-zcash/ragu/compare/ragu_circuits-0.0.0...HEAD
[0.0.0]: https://github.com/tachyon-zcash/ragu/releases/tag/ragu_circuits-0.0.0
