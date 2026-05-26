import Clean.Circuit
import Ragu.Core
import Ragu.Circuits.Core.Mul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

/-- `Input` carries the numerator `x`, the divisor `y`, and a prover hint
with `1 / y` used by the in-circuit `enforce_nonzero(y)` discharge. -/
structure Input (F : Type) where
  x : F
  y : F
  inverse : UnconstrainedDep field F
deriving CircuitType

/-- `Element::divide(&y_nonzero)` after `y.enforce_nonzero(...)`.

  This reimpl inlines both halves so the new wire `a` allocated by
  `Invertible::alloc` is in scope when the divide step links its
  denominator. Step by step:

  1. **Discharge** — `Invertible::alloc(y)` allocates `(a, b, c)` with
     `a · b = c`, then enforces `c = 1` and `y = a`. After this `a` is
     constrained equal to `y` and is provably nonzero.
  2. **Divide** — allocates `(quotient, denominator, numerator)` with
     `quotient · denominator = numerator`, then enforces
     `x = numerator` and `a = denominator` (using the discharged wire
     `a`, mirroring `Rust::divide` which uses `y_nonzero.wire()`). -/
def main (input : Var Input (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨x, y, inverse⟩ := input
  -- enforce_nonzero(y)
  let ⟨a, _b, c⟩ ← Core.mul fun env =>
    ⟨env y, inverse env, 1⟩
  assertZero (c - 1)
  assertZero (y - a)
  -- divide(x, &y_nonzero)
  let ⟨quotient, denominator, numerator⟩ ← Core.mul fun env =>
    ⟨(env x) / (env y), env y, env x⟩
  assertZero (x - numerator)
  assertZero (a - denominator)
  return quotient

/-- Verifier side: the circuit *itself* discharges `y ≠ 0` via the
`Invertible::alloc` half, so no precondition is required for soundness.
The spec pins `out = x / y`. -/
def Spec (input : Value Input (F p))
    (out : field (F p)) (_data : ProverData (F p)) :=
  out = input.x / input.y

/-- Prover-side assumptions: `y ≠ 0` so the supplied inverse hint is
coherent. -/
def ProverAssumptions (input : ProverValue Input (F p))
    (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  let yValue : F p := input.y
  let inverse : F p := input.inverse
  yValue * inverse = 1

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  output _ offset := varFromOffset field (offset + 3)
  localLength _ := 6

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start
  obtain ⟨h_mul1, h_c, h_lin1, h_mul2, h_lin2, h_lin3⟩ := h_holds
  -- h_mul1 : a · b = c
  -- h_c    : c - 1 = 0
  -- h_lin1 : y - a = 0
  -- h_mul2 : quotient · denominator = numerator
  -- h_lin2 : x - numerator = 0
  -- h_lin3 : a - denominator = 0
  rw [add_neg_eq_zero] at h_c h_lin1 h_lin2 h_lin3
  rw [← h_lin1, h_c] at h_mul1
  -- h_mul1 : y · b = 1
  rw [← h_lin2, ← h_lin3, ← h_lin1] at h_mul2
  -- h_mul2 : quotient · y = x
  have hy : (input_y : F p) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h_mul1
    exact zero_ne_one h_mul1
  exact (eq_div_iff hy).mpr h_mul2

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (F p) elaborated ProverAssumptions
      (fun _ _ _ => True) := by
  circuit_proof_start
  grind

def circuit : GeneralFormalCircuit.WithHint (F p) Input field where
  elaborated
  Spec
  ProverAssumptions
  soundness
  completeness

end Ragu.Circuits.Element.DivNonzero
