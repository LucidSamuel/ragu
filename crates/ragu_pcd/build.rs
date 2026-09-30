//! Cargo entry point for generating the baked Pasta parameters.

use std::{env, path::PathBuf};

#[path = "src/pasta/generate.rs"]
mod generate;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src/pasta/generate.rs");

    if env::var("CARGO_FEATURE_BAKED").is_err() {
        return;
    }

    let out_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    generate::write_parameters(&out_dir).unwrap();
}
