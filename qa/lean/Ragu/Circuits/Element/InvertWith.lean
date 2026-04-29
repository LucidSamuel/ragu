import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.InvertWith
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  input : F
  hint : UnconstrainedDep Core.AllocMul.Row F
deriving CircuitType

@[circuit_norm] lemma eval_verifier {F : Type} [Field F] (env : Environment F) (input : Var Input F) :
  eval env input = CircuitType.evalVerifier env input := CircuitType.eval_verifier env input

@[circuit_norm] lemma eval_prover {F : Type} [Field F] (env : ProverEnvironment F) (input : Var Input F) :
  eval env input = CircuitType.evalProver env input := CircuitType.eval_prover env input

/-- `invert_with` allocates a mul gate `(a, b, c)` with `a·b = c`, then
enforces `a = input` and `c = 1`, returning `b` as the inverse wire. -/
def main (input : Var Input (F p))
    : Circuit (F p) (Expression (F p)) := do
  let ⟨input, hint⟩ := input
  let ⟨a, b, c⟩ ← Core.AllocMul.circuit hint
  assertZero (a - input)
  assertZero (c - 1)
  return b

def Assumptions (_input : Value Input (F p))
    (_data : ProverData (F p)) := True

def ProverAssumptions (input : ProverValue Input (F p))
    (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  input.hint.x = input.input ∧ input.hint.x * input.hint.y = 1

def Spec (input : Value Input (F p))
    (out : F p) (_data : ProverData (F p)) :=
  let inputValue : F p := input.input
  inputValue * out = 1

instance elaborated
    : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 3

theorem soundness
    : GeneralFormalCircuit.WithHint.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Spec
  ]
  obtain ⟨h_mul, h_a, h_c⟩ := h_holds
  rw [add_neg_eq_zero] at h_a h_c
  rw [h_a, h_c] at h_mul
  rw [← h_input]
  exact h_mul

theorem completeness
    : GeneralFormalCircuit.WithHint.Completeness (F p) elaborated
        ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Spec, Core.AllocMul.ProverSpec
  ]
  obtain ⟨_, h_x_eq, h_y_eq, h_z_eq⟩ := h_env
  rw [← h_input] at h_assumptions
  simp [ProverAssumptions, circuit_norm] at h_assumptions
  obtain ⟨h_x_in, h_prod_in⟩ := h_assumptions
  rw [add_neg_eq_zero, add_neg_eq_zero]
  refine ⟨?_, ?_⟩
  · rw [h_x_eq]; exact h_x_in
  · rw [h_z_eq]; exact h_prod_in

def circuit : GeneralFormalCircuit.WithHint (F p) Input field :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    ProverAssumptions := ProverAssumptions,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Element.InvertWith
