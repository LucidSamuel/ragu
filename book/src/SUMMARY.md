# Summary

[Introduction](introduction.md)
[Proof-carrying data](concepts/pcd.md)

---

- [Part I: User Guide]()
  - [Requirements](guide/requirements.md)
  - [Getting Started](guide/getting_started.md) <!-- todo -->
  - [Drivers](guide/drivers/index.md)
    - [Witness Data](guide/drivers/witness.md)
    - [Linear Expressions](guide/drivers/linear.md)
    - [Concrete Drivers](guide/drivers/concrete.md)
  - [Gadgets](guide/gadgets/index.md)
    - [Simple Gadgets](guide/gadgets/simple.md)
    - [The GadgetKind Trait](guide/gadgets/gadgetkind.md)
    - [The Kind! Macro](guide/gadgets/kind.md)
    - [Conversion](guide/gadgets/conversion.md)
  - [Routines](guide/routines.md)
  - [Writing Circuits](guide/writing_circuits.md) <!-- todo -->
  - [Configuration](guide/configuration.md) <!-- todo -->
- [Part II: Protocol Design]()
  - [Overview](protocol/index.md) <!-- todo -->
  - [Preliminaries]()
    - [Cryptographic Assumptions](protocol/prelim/assumptions.md)
    - [Notation](protocol/prelim/notation.md)
    - [Structured Vectors](protocol/prelim/structured_vectors.md)
    - [Nested Commitment](protocol/prelim/nested_commitment.md)
    - [Bulletproofs IPA](protocol/prelim/bulletproofs.md)
    - [Transcript](protocol/prelim/transcript.md)
  - [Core Construction]()
    - [Arithmetization](protocol/core/arithmetization.md)
    - [NARK](protocol/core/nark.md)
    - [Split-Accumulation Schemes](protocol/core/accumulation/index.md)
      - [PCS Batched Evaluation](protocol/core/accumulation/pcs.md)
      - [Wiring Consistency](protocol/core/accumulation/wiring.md)
      - [Revdot Product](protocol/core/accumulation/revdot.md)
  - [Extensions]()
    - [Registry Polynomial](protocol/extensions/registry.md)
    - [Endoscalars](protocol/extensions/endoscalar.md)
    - [Staging](protocol/extensions/staging.md)
  - [Recursion]()
    - [Public Inputs](protocol/recursion/public_inputs.md) <!-- todo -->
  - [Analysis](protocol/analysis.md)
- [Part III: Implementation]()
  - [Architecture Overview](implementation/arch.md) <!-- todo -->
  - [Circuits](implementation/circuits.md) <!-- todo -->
  - [Polynomial Management](implementation/polynomials.md) <!-- todo -->
  - [PCD Step and Proofs](implementation/proofs.md) <!-- todo -->
  - [Staging](implementation/staging.md) <!-- todo -->
  - [Drivers]()
    - [Writing Custom Drivers](implementation/drivers/custom.md) <!-- todo -->

---

# Appendices

- [Bootle16 v.s. R1CS](appendix/cs.md)
- [Related Work](appendix/related.md) <!-- todo -->
- [SNARKs](appendix/snarks.md)
- [Terminology](appendix/terminology.md)
