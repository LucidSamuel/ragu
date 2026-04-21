import Clean.Circuit

namespace Ragu.Circuits.Element.Scale
variable {p : ℕ} [Fact p.Prime]

def main (coeff : F p) (input : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  return coeff * input

def Assumptions (_coeff : F p) (_input : F p) := True

def Spec (coeff : F p) (input : F p) (output : F p) :=
  output = coeff * input

instance elaborated (coeff : F p) : ElaboratedCircuit (F p) field field where
  main := main coeff
  localLength _ := 0

theorem soundness (coeff : F p) :
    Soundness (F p) (elaborated coeff) (Assumptions coeff) (Spec coeff) := by
  circuit_proof_start

theorem completeness (coeff : F p) :
    Completeness (F p) (elaborated coeff) (Assumptions coeff) := by
  circuit_proof_start

def circuit (coeff : F p) : FormalCircuit (F p) field field :=
  { elaborated coeff with
    Assumptions := Assumptions coeff,
    Spec := Spec coeff,
    soundness := soundness coeff,
    completeness := completeness coeff }

end Ragu.Circuits.Element.Scale
