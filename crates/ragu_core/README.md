<p align="center">
  <img width="300" height="80" src="https://tachyon.z.cash/assets/ragu/v1/github-600x160.png">
</p>

# `ragu_core`

This crate contains internal implementation code for the [`ragu`](https://crates.io/crates/ragu) crate.

This crate reexports Udon's cycle and Poseidon interfaces and exposes its
Pasta types through [`pasta`](src/lib.rs). Ragu's fixed generator derivation
and loading live in `ragu_pcd::pasta`. The field and curve arithmetic, Pasta
cycle types, and Poseidon constants come from `udon`.

## License

This library is distributed under the terms of both the MIT license and the Apache License (Version 2.0). See [LICENSE-APACHE](./LICENSE-APACHE), [LICENSE-MIT](./LICENSE-MIT) and [COPYRIGHT](./COPYRIGHT).
