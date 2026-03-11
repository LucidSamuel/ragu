import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  x : F
  y : F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨quotient, denominator, numerator⟩ ← subcircuit Core.AllocMul.circuit default

  assertZero (input.x - numerator)
  assertZero (input.y - denominator)

  return quotient

def Assumptions (input : Inputs (F p)) := input.y ≠ 0

def Spec (input : Inputs (F p)) (out : field (F p)) :=
  out = input.x / input.y

instance elaborated : ElaboratedCircuit (F p) Inputs field where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp [circuit_norm, Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec] at h_holds ⊢
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c2 c3
  rw [←c2, ←c3] at c1
  apply eq_div_of_mul_eq <;> assumption

theorem completeness : Completeness (F p) elaborated Assumptions := by
  sorry

def circuit : FormalCircuit (F p) Inputs field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.DivNonzero
