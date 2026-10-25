# Requirements

* The minimum supported [Rust](https://rust-lang.org/) version is currently
  **1.97.1**.
* Ragu requires minimal dependencies and currently strives to avoid using
  dependencies that are not already used in
  [Zebra](https://github.com/ZcashFoundation/zebra).

## `no_std` Support {#no-std}

None of Ragu's library code requires the standard library. Every
library crate is `#![no_std]`.

Ragu does need a global allocator, since the library uses `Vec`,
`Box`, and similar heap types from the [`alloc`] crate. That means it
is happy on targets with an allocator but no full `std` runtime —
WebAssembly and embedded platforms, for example.

`ragu_core`, `ragu_primitives`, `ragu_circuits`, and `ragu_pcd` enable only
`alloc` by default; keep it enabled when disabling default features. The
`multicore` feature of `ragu_pcd` is opt-in; it pulls in `std` via
[maybe-rayon] for multi-threaded parallelism.

[`alloc`]: https://doc.rust-lang.org/alloc/
[maybe-rayon]: https://crates.io/crates/maybe-rayon
