import Clean.Circuit
import Ragu.Circuits.Element.InvertWith

namespace Ragu.Circuits.Element.Invert
variable {p : ℕ} [Fact p.Prime]

abbrev Input := InvertWith.Input

/-- `Element::invert(input)` delegates to `invert_with` with an inverse
witness derived from the input. The Lean reimpl mirrors that delegation
directly via the `InvertWith` subcircuit; the only added obligation is
the caller's `input ≠ 0` (otherwise the inverse doesn't exist and the
honest prover can't satisfy `b · input = 1`). -/
def main (input : Var Input (F p))
    : Circuit (F p) (Expression (F p)) := do
  InvertWith.circuit input

def Assumptions (_input : Value Input (F p))
    (_data : ProverData (F p)) := True

/-- Stronger than `invert_with`'s assumption: the caller must additionally
promise `input ≠ 0`. The hint preconditions delegate to `InvertWith`. -/
def ProverAssumptions (input : ProverValue Input (F p))
    (data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let inputValue : F p := input.input
  InvertWith.ProverAssumptions input data hint ∧ inputValue ≠ 0

def Spec (input : Value Input (F p))
    (out : F p) (data : ProverData (F p)) :=
  InvertWith.Spec input out data

instance elaborated
    : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 3

theorem soundness
    : GeneralFormalCircuit.WithHint.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [InvertWith.circuit, InvertWith.Spec]
  exact h_holds trivial

theorem completeness
    : GeneralFormalCircuit.WithHint.Completeness (F p) elaborated
        ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start [InvertWith.circuit, InvertWith.ProverAssumptions]
  exact h_assumptions.1

def circuit : GeneralFormalCircuit.WithHint (F p) Input field :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    ProverAssumptions := ProverAssumptions,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Element.Invert
