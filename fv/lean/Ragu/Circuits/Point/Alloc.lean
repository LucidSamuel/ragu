import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Alloc
variable {p : ℕ} [Fact p.Prime]

def main (curveParams : Spec.CurveParams p) (idx : ℕ) (_input : Unit) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x, x_sq⟩ ← Element.AllocSquare.generalCircuit idx ()
  let x3 ← Element.Mul.circuit ⟨x, x_sq⟩
  let ⟨y, y_sq⟩ ← Element.AllocSquare.generalCircuit (idx + 2) ()
  assertZero ((x3 + (curveParams.b * 1)) - y_sq)
  return ⟨x, y⟩

def Assumptions (curveParams : Spec.CurveParams p) (idx : ℕ) (_input : Unit) (data : ProverData (F p)) :=
  (Element.AllocSquare.readInput data idx)^3 + curveParams.b =
    (Element.AllocSquare.readInput data (idx + 2))^2

def Spec (curveParams : Spec.CurveParams p) (_input : Unit) (out : Spec.Point (F p)) (_data : ProverData (F p)) :=
  out.isOnCurve curveParams

instance elaborated (curveParams : Spec.CurveParams p) (idx : ℕ) : ElaboratedCircuit (F p) unit Spec.Point where
  main := main curveParams idx
  localLength _ := 9

theorem soundness (curveParams : Spec.CurveParams p) (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated curveParams idx) (Spec curveParams) := by
  circuit_proof_start [
    Element.AllocSquare.generalCircuit, Element.AllocSquare.Assumptions,
    Element.AllocSquare.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  simp only [Spec.Point.isOnCurve]
  obtain ⟨h_sq_x, h_mul, h_sq_y, h_assert⟩ := h_holds
  rw [add_neg_eq_zero, mul_one] at h_assert
  rw [← h_sq_y, ← h_assert, h_mul, h_sq_x]
  ring

theorem completeness (curveParams : Spec.CurveParams p) (idx : ℕ) : GeneralFormalCircuit.Completeness (F p) (elaborated curveParams idx) (Assumptions curveParams idx) := by
  circuit_proof_start [
    Element.AllocSquare.generalCircuit, Element.AllocSquare.Assumptions,
    Element.AllocSquare.Spec, Element.AllocSquare.CompletenessSpec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  obtain ⟨⟨_, h_x, h_xsq⟩, h_mul, ⟨_, _, h_ysq⟩⟩ := h_env
  rw [h_mul, h_x, h_xsq, h_ysq, mul_one, add_neg_eq_zero]
  rw [show Element.AllocSquare.readInput env.data idx *
    Element.AllocSquare.readInput env.data idx ^ 2 =
    Element.AllocSquare.readInput env.data idx ^ 3 from by ring]
  exact h_assumptions

def circuit (curveParams : Spec.CurveParams p) (idx : ℕ) : GeneralFormalCircuit (F p) unit Spec.Point :=
  {
    (elaborated curveParams idx) with
    Assumptions := Assumptions curveParams idx,
    Spec := (Spec curveParams),
    soundness := soundness curveParams idx,
    completeness := completeness curveParams idx
  }

end Ragu.Circuits.Point.Alloc
