import Clean.Circuit
import Ragu.Circuits.Element.InvertWith

namespace Ragu.Circuits.Element.Invert
variable {p : ℕ} [Fact p.Prime]

/-- `Element::invert(input)` delegates to `invert_with` with an inverse
witness derived from the input. The Lean reimpl mirrors that delegation
directly via the `InvertWith` subcircuit; the only added obligation is
the caller's `input ≠ 0` (otherwise the inverse doesn't exist and the
honest prover can't satisfy `b · input = 1`). -/
def main (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p)) (input : Expression (F p))
    : Circuit (F p) (Expression (F p)) := do
  InvertWith.circuit hintReader input

/-- Stronger than `invert_with`'s assumption: the caller must additionally
promise `input ≠ 0`. The hint preconditions delegate to `InvertWith`. -/
def Assumptions (_input : F p) (_data : ProverData (F p)) := True

def ProverAssumptions (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    (input : F p) (data : ProverData (F p)) (hint : ProverHint (F p)) :=
  InvertWith.ProverAssumptions hintReader input data hint ∧ input ≠ 0

def Spec (input : F p) (out : F p) (data : ProverData (F p)) :=
  InvertWith.Spec input out data

instance elaborated (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : ElaboratedCircuit (F p) field field where
  main := main hintReader
  localLength _ := 3

theorem soundness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Soundness (F p) (elaborated hintReader) Assumptions Spec := by
  circuit_proof_start [InvertWith.circuit, InvertWith.Spec]
  exact h_holds trivial

theorem completeness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Completeness (F p) (elaborated hintReader)
        (ProverAssumptions hintReader) (fun _ _ _ => True) := by
  circuit_proof_start [InvertWith.circuit, InvertWith.ProverAssumptions]
  exact h_assumptions.1

def circuit (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit (F p) field field :=
  { elaborated hintReader with
    Assumptions := Assumptions,
    Spec := Spec,
    ProverAssumptions := ProverAssumptions hintReader,
    soundness := soundness hintReader,
    completeness := completeness hintReader }

end Ragu.Circuits.Element.Invert
