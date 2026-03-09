import Clean.Circuit
import Clean.Utils.Primes

namespace Ragu.Circuits.Point.Alloc
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

@[reducible]
def Inputs := unit

structure Point (F : Type) where
  x : F
  y : F
deriving ProvableStruct


def main (_input : Inputs (F p)) : Circuit (F p) (Var Point (F p)) := do
  let x <- witness fun _env => default
  let y <- witness fun _env => default
  assertZero (x*x*x + 5 - y*y)
  return ⟨x, y⟩


def Assumptions (_inputs : Inputs (F p)) := True

def Spec (_inputsinputs : Unit) (out_point : Point (F p)) :=
  out_point.x^3 + 5 = out_point.y^2

#eval! main (p:=pBabybear) default |>.operations 0
instance elaborated : ElaboratedCircuit (F p) Inputs Point where
  main
  localLength _ := 2


theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  sorry

def circuit : FormalCircuit (F p) unit Point :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Point.Alloc
