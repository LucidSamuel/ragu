//! Verifier-consulted kernels.
//!
//! The [`Backend`](ragu_backend::Backend) trait has a single set of methods,
//! and the prover uses all of them. Some of them are *also* what
//! `ragu_pcd`'s verifier uses to compute the left-hand side of its acceptance
//! comparisons, whenever the selected backend's `Verifier` is the
//! accelerated one (`AcceleratedBackend`, but not `AcceleratedProver`): the
//! sparse polynomial evaluations and reverse inner products, the registry
//! restrictions, and the batched commitment check, which runs through
//! `sparse_commit_to_affine` and so through `msm`. An override of any of
//! those is shared by the prover and the verifier; it is implemented in this
//! module and reached from the `Backend` impl in the crate root by
//! delegation, so the code that can influence an acceptance decision is
//! confined to one place and can be tested directly.
//!
//! The one override today is `msm`, in this module's `msm` submodule.

pub(crate) mod msm;
