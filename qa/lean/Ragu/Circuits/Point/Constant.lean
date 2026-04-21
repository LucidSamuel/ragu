import Clean.Circuit
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Constant
variable {p : ℕ} [Fact p.Prime]

/-- `Point::constant(P)` lifts a concrete curve point into the circuit as a
pair of constant wires. Zero ops emitted; output wires are
`(Expression.const P.x, Expression.const P.y)`. Parameterized over the
chosen point's coordinates. -/
def main (px py : F p) (_input : Unit) : Circuit (F p) (Var Spec.Point (F p)) := do
  return { x := Expression.const px, y := Expression.const py }

def Assumptions (_px _py : F p) (_input : Unit) := True

def Spec (px py : F p) (_input : Unit) (output : Spec.Point (F p)) :=
  output.x = px ∧ output.y = py

instance elaborated (px py : F p) : ElaboratedCircuit (F p) unit Spec.Point where
  main := main px py
  localLength _ := 0

theorem soundness (px py : F p) :
    Soundness (F p) (elaborated px py) (Assumptions px py) (Spec px py) := by
  circuit_proof_start

theorem completeness (px py : F p) :
    Completeness (F p) (elaborated px py) (Assumptions px py) := by
  circuit_proof_start

def circuit (px py : F p) : FormalCircuit (F p) unit Spec.Point :=
  { elaborated px py with
    Assumptions := Assumptions px py,
    Spec := Spec px py,
    soundness := soundness px py,
    completeness := completeness px py }

end Ragu.Circuits.Point.Constant
