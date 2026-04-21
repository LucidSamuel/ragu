import Clean.Circuit

namespace Ragu.Circuits.Element.Double
variable {p : ℕ} [Fact p.Prime]

def main (input : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  return input + input

def Assumptions (_input : F p) := True

def Spec (input : F p) (output : F p) :=
  output = input + input

instance elaborated : ElaboratedCircuit (F p) field field where
  main
  localLength _ := 0

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start

def circuit : FormalCircuit (F p) field field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.Double
