import Clean.Circuit
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Boolean.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- `Boolean::alloc` constrains a wire to hold `0` or `1`.

Delegates the 3-wire `a * b = c` gate to `Core.AllocMul`, then
asserts `c = 0` (collapsing the gate to `a * b = 0`) and
`1 - a - b = 0` (binding `b = 1 - a`). Together: `a * (1 - a) = 0`, so
`a ∈ {0, 1}`. -/
def main (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p)) (_input : Unit)
    : Circuit (F p) (Var field (F p)) := do
  let ⟨a, b, c⟩ ← Core.AllocMul.circuit hintReader ()
  assertZero c
  assertZero (1 - a - b)
  return a

/-- For completeness, the hint must describe a valid boolean row:
`r.x + r.y = 1` (so the linear constraint holds) and `r.x * r.y = 0`
(so the gate constraint reduces to `c = 0`). Over a field these
together force `r.x, r.y ∈ {0, 1}`. -/
def Assumptions (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    (_input : Unit) (_data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let r := hintReader hint
  r.x + r.y = 1 ∧ r.x * r.y = 0

/-- The verifier learns the output wire is boolean-valued. -/
def Spec (_input : Unit) (out : F p) (_data : ProverData (F p)) :=
  out = 0 ∨ out = 1

instance elaborated (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : ElaboratedCircuit (F p) unit field where
  main := main hintReader
  localLength _ := 3

theorem soundness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Soundness (F p) (elaborated hintReader) Spec := by
  circuit_proof_start [Core.AllocMul.circuit, Core.AllocMul.Spec]
  obtain ⟨h_mul, h_c, h_lin⟩ := h_holds
  -- h_mul : a * b = c, h_c : c = 0, h_lin : 1 - a - b = 0
  rw [h_c] at h_mul
  rcases mul_eq_zero.mp h_mul with ha | hb
  · exact Or.inl ha
  · exact Or.inr (by linear_combination -h_lin - hb)

theorem completeness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Completeness (F p) (elaborated hintReader) (Assumptions hintReader) := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions,
    Core.AllocMul.CompletenessSpec
  ]
  obtain ⟨h_sum, h_prod⟩ := h_assumptions
  obtain ⟨_, hx, hy, hz⟩ := h_env
  -- hx : a = r.x, hy : b = r.y, hz : c = r.x * r.y
  refine ⟨?_, ?_⟩
  · rw [hz]; exact h_prod
  · rw [hx, hy]; linear_combination -h_sum

def circuit (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit (F p) unit field :=
  { elaborated hintReader with
    Assumptions := Assumptions hintReader,
    Spec := Spec,
    soundness := soundness hintReader,
    completeness := completeness hintReader }

end Ragu.Circuits.Boolean.Alloc
