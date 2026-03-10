import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.Mul
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

def main (input : Var Input (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨x, y, z⟩ <- Ragu.Circuits.Core.AllocMul.circuit.main default
  assertZero (x - input.x)
  assertZero (y - input.y)
  return z


def Assumptions (_input : Input (F p)) := True

def Spec (input : Input (F p)) (out : field (F p)) :=
  out = input.x * input.y

-- #eval! main (p:=pBabybear) default |>.operations 0
instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  sorry

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.Mul
