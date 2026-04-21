import Clean.Circuit

namespace Ragu.Circuits.Element.Add
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  return input.x + input.y

def Assumptions (_input : Input (F p)) := True

def Spec (input : Input (F p)) (output : F p) :=
  output = input.x + input.y

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 0

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.Add
