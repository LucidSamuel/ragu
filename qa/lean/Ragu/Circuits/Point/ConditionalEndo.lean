import Clean.Circuit
import Ragu.Circuits.Core.AllocMul
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.ConditionalEndo
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  cond : F
  x : F
  y : F
deriving ProvableStruct

/-- `Point::conditional_endo(cond)` is a composite:
`self.x.scale(ζ)` (virtual), then `cond.conditional_select(self.x, endo_x)`
(one mul gate + 2 enforce_equals), then reassemble as a Point with the
selected x-coordinate and the unchanged y. -/
def main (curveParams : Spec.CurveParams p) (input : Var Input (F p))
    : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x1, y, z⟩ ← (witness fun env =>
    let cv := Expression.eval env input.cond
    let xv := Expression.eval env input.x
    let diff := curveParams.ζ * xv - xv
    (⟨cv, diff, cv * diff⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x1 * y - z)
  assertZero (x1 - input.cond)
  assertZero (y - (curveParams.ζ * input.x - input.x))
  return ⟨input.x + z, input.y⟩

/-- Caller must promise `cond ∈ {0, 1}`; the algebraic `Spec` holds
unconditionally, but is only meaningful as a "conditional endomorphism"
under this precondition. -/
def Assumptions (_curveParams : Spec.CurveParams p) (input : Input (F p)) :=
  input.cond = 0 ∨ input.cond = 1

/-- Matches the Rust formula: the new x is `x + cond * (ζ·x - x)` and the
new y is unchanged. Under `cond = 0` the x is unchanged; under `cond = 1`
the x becomes `ζ·x`. -/
def Spec (curveParams : Spec.CurveParams p) (input : Input (F p))
    (output : Spec.Point (F p)) :=
  output.x = input.x + input.cond * (curveParams.ζ * input.x - input.x) ∧
  output.y = input.y

instance elaborated (curveParams : Spec.CurveParams p)
    : ElaboratedCircuit (F p) Input Spec.Point where
  main := main curveParams
  localLength _ := 3

theorem soundness (curveParams : Spec.CurveParams p)
    : Soundness (F p) (elaborated curveParams) (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c3
  rw [← c1, c2, c3]
  ring

theorem completeness (curveParams : Spec.CurveParams p)
    : Completeness (F p) (elaborated curveParams) (Assumptions curveParams) := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  refine ⟨?_, ?_, ?_⟩ <;> ring

def circuit (curveParams : Spec.CurveParams p) : FormalCircuit (F p) Input Spec.Point :=
  { elaborated curveParams with
    Assumptions := Assumptions curveParams,
    Spec := Spec curveParams,
    soundness := soundness curveParams,
    completeness := completeness curveParams }

end Ragu.Circuits.Point.ConditionalEndo
