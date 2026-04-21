import Clean.Circuit

namespace Ragu.Circuits.Element.AddCoeff
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

def main (coeff : F p) (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  return input.x + coeff * input.y

def Assumptions (_coeff : F p) (_input : Input (F p)) := True

def Spec (coeff : F p) (input : Input (F p)) (output : F p) :=
  output = input.x + coeff * input.y

instance elaborated (coeff : F p) : ElaboratedCircuit (F p) Input field where
  main := main coeff
  localLength _ := 0

theorem soundness (coeff : F p) :
    Soundness (F p) (elaborated coeff) (Assumptions coeff) (Spec coeff) := by
  circuit_proof_start

theorem completeness (coeff : F p) :
    Completeness (F p) (elaborated coeff) (Assumptions coeff) := by
  circuit_proof_start

def circuit (coeff : F p) : FormalCircuit (F p) Input field :=
  { elaborated coeff with
    Assumptions := Assumptions coeff,
    Spec := Spec coeff,
    soundness := soundness coeff,
    completeness := completeness coeff }

end Ragu.Circuits.Element.AddCoeff
