import Clean.Circuit
import Ragu.Core
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.EnforceNonzero

namespace Ragu.Circuits.NonzeroBank.ScopeK2
variable {p : ℕ} [Fact p.Prime]

/-- `Input` carries the two factors and a prover hint for the inverse of
their product, used by the discharge at scope end. -/
structure Input (F : Type) where
  f1 : F
  f2 : F
  inverse : UnconstrainedDep field F
deriving CircuitType

/-- Packages `NonzeroBank::scope` over `K = 2` factors. Mirrors the
Rust extraction body:

```rust
NonzeroBank::scope(dr, |dr, bank| {
    bank.fold(dr, f1)?;
    bank.fold(dr, f2)?;
    Ok(())
})
```

Each `bank.fold` in discharging mode multiplies the new factor into the
running product (one `Element::mul`); at scope end the bank discharges
`product ≠ 0` via `Element::enforce_nonzero`. By multiplicative
integrality (`F` is a field), `product ≠ 0` implies each factor is
nonzero — that's the reusable lemma. -/
def main (input : Var Input (F p)) : Circuit (F p) Unit := do
  let ⟨f1, f2, inverse⟩ := input
  -- fold 1: running product = 1 * f1
  let p1 ← Element.Mul.circuit ⟨1, f1⟩
  -- fold 2: running product = p1 * f2
  let p2 ← Element.Mul.circuit ⟨p1, f2⟩
  -- discharge: p2 ≠ 0
  Element.EnforceNonzero.circuit { input := p2, inverse }

/-- Verifier side: the discharge witnesses that the running product is
nonzero, which (since `F p` is a field) implies each factor is
nonzero. -/
def Spec (input : Value Input (F p))
    (_out : Unit) (_data : ProverData (F p)) :=
  input.f1 ≠ 0 ∧ input.f2 ≠ 0

/-- Prover side: needs both factors nonzero so the running product is
invertible and the supplied inverse hint is coherent. -/
def ProverAssumptions (input : ProverValue Input (F p))
    (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  let f1 : F p := input.f1
  let f2 : F p := input.f2
  let inverse : F p := input.inverse
  (f1 * f2) * inverse = 1

instance elaborated : ElaboratedCircuit (F p) Input unit where
  main
  output _ _ := ()
  localLength _ := 9

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start [Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec,
    Element.EnforceNonzero.circuit, Element.EnforceNonzero.Spec]
  obtain ⟨h_p1, h_p2, h_nz⟩ := h_holds
  -- h_p1 : p1 = f1 (since Mul₁ folds 1 * f1)
  -- h_p2 : p2 = p1 * f2
  -- h_nz : p2 ≠ 0
  rw [h_p1] at h_p2
  rw [h_p2] at h_nz
  refine ⟨?_, ?_⟩
  · intro h; exact h_nz (by rw [h, zero_mul])
  · intro h; exact h_nz (by rw [h, mul_zero])

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (F p) elaborated ProverAssumptions
      (fun _ _ _ => True) := by
  circuit_proof_start [Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec,
    Element.EnforceNonzero.circuit, Element.EnforceNonzero.Spec,
    Element.EnforceNonzero.ProverAssumptions]
  obtain ⟨h_p1, h_p2, _⟩ := h_env
  rw [h_p2, h_p1]
  exact h_assumptions

def circuit : GeneralFormalCircuit.WithHint (F p) Input unit where
  elaborated
  Spec
  ProverAssumptions
  soundness
  completeness

end Ragu.Circuits.NonzeroBank.ScopeK2
