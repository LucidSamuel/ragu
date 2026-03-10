import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

def main (_input : Unit) : Circuit (F p) (Var Square (F p)) := do
  let ⟨x, y, z⟩ <- Ragu.Circuits.Core.AllocMul.circuit.main default
  assertZero (x - y)
  return ⟨x, z⟩


def Assumptions (_input : Unit) := True

def Spec (_input : Unit) (out : Square (F p)) :=
  out.a_sq = out.a * out.a

-- #eval! main (p:=pBabybear) default |>.operations 0
instance elaborated : ElaboratedCircuit (F p) unit Square where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  sorry

def circuit : FormalCircuit (F p) unit Square :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.AllocSquare
