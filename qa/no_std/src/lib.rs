//! A consumer of baked Pasta parameters, compiled for bare metal by backend CI.

#![no_std]

use ragu_pcd::pasta::PastaParams;

/// Obtains the parameters through the public API without requiring `std`.
pub fn parameters() -> &'static PastaParams {
    ragu_pcd::pasta::baked()
}
