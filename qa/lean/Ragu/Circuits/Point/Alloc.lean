import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- The allocator reads two field elements from `hint "alloc_square_w" 1`:
    one at index `xIdx` for the x-coordinate, one at index `yIdx` for y. -/
def main (curveParams : Spec.CurveParams p) (xIdx yIdx : ℕ)
    (_input : Unit) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x, x_sq⟩ ← Element.AllocSquare.generalCircuit "alloc_square_w" 1 xIdx 0 ()
  let x3 ← Element.Mul.circuit ⟨x, x_sq⟩
  let ⟨y, y_sq⟩ ← Element.AllocSquare.generalCircuit "alloc_square_w" 1 yIdx 0 ()
  assertZero ((x3 + (curveParams.b * 1)) - y_sq)
  return ⟨x, y⟩

def Assumptions (curveParams : Spec.CurveParams p) (xIdx yIdx : ℕ)
    (_input : Unit) (_data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let hx := Element.AllocSquare.readElem hint "alloc_square_w" 1 xIdx 0
  let hy := Element.AllocSquare.readElem hint "alloc_square_w" 1 yIdx 0
  hx ^ 3 + curveParams.b = hy ^ 2

def Spec (curveParams : Spec.CurveParams p) (_input : Unit) (out : Spec.Point (F p)) (_data : ProverData (F p)) :=
  out.isOnCurve curveParams

instance elaborated (curveParams : Spec.CurveParams p) (xIdx yIdx : ℕ)
    : ElaboratedCircuit (F p) unit Spec.Point where
  main := main curveParams xIdx yIdx
  localLength _ := 9

theorem soundness (curveParams : Spec.CurveParams p) (xIdx yIdx : ℕ) :
    GeneralFormalCircuit.Soundness (F p) (elaborated curveParams xIdx yIdx) (Spec curveParams) := by
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

theorem completeness (curveParams : Spec.CurveParams p) (xIdx yIdx : ℕ) :
    GeneralFormalCircuit.Completeness (F p) (elaborated curveParams xIdx yIdx)
      (Assumptions curveParams xIdx yIdx) := by
  circuit_proof_start [
    Element.AllocSquare.generalCircuit, Element.AllocSquare.Assumptions,
    Element.AllocSquare.Spec, Element.AllocSquare.CompletenessSpec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  obtain ⟨⟨_, h_x, h_xsq⟩, h_mul, ⟨_, _, h_ysq⟩⟩ := h_env
  rw [h_mul, h_x, h_xsq, h_ysq, mul_one, add_neg_eq_zero]
  set hx := Element.AllocSquare.readElem env.hint "alloc_square_w" 1 xIdx 0
  set hy := Element.AllocSquare.readElem env.hint "alloc_square_w" 1 yIdx 0
  rw [show hx * hx ^ 2 = hx ^ 3 from by ring]
  exact h_assumptions

def circuit (curveParams : Spec.CurveParams p) (xIdx yIdx : ℕ) :
    GeneralFormalCircuit (F p) unit Spec.Point :=
  {
    (elaborated curveParams xIdx yIdx) with
    Assumptions := Assumptions curveParams xIdx yIdx,
    Spec := (Spec curveParams),
    soundness := soundness curveParams xIdx yIdx,
    completeness := completeness curveParams xIdx yIdx
  }

end Ragu.Circuits.Point.Alloc
