import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Boolean.And
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  a : F
  b : F
deriving ProvableStruct

/-- `Boolean::and` emits one mul gate (`x · y = z`) and two `enforce_equal`s
binding the gate's `x`/`y` wires to the input boolean wires. Returns the
gate's `z` wire as the output. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let av := Expression.eval env input.a
    let bv := Expression.eval env input.b
    (⟨av, bv, av * bv⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - input.a)
  assertZero (y - input.b)
  return z

/-- Caller must promise the inputs are boolean. Without this the output
may not itself be boolean (though it would still equal `a * b`). -/
def Assumptions (input : Input (F p)) :=
  (input.a = 0 ∨ input.a = 1) ∧ (input.b = 0 ∨ input.b = 1)

/-- The output is the product — and, under the boolean assumption,
equivalently the logical AND. The output is itself boolean-valued, so
downstream consumers can treat the returned wire as a `Boolean`. -/
def Spec (input : Input (F p)) (out : F p) :=
  out = input.a * input.b ∧ (out = 0 ∨ out = 1)

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c3
  obtain ⟨ha, hb⟩ := h_assumptions
  refine ⟨?_, ?_⟩
  · -- out = a * b
    rw [←c2, ←c3, c1]
  · -- out ∈ {0, 1}: case-split on the boolean inputs.
    rcases ha with ha0 | ha1
    · left
      rw [← c1, c2, ha0, zero_mul]
    · rcases hb with hb0 | hb1
      · left
        rw [← c1, c2, c3, ha1, hb0, mul_zero]
      · right
        rw [← c1, c2, c3, ha1, hb1, mul_one]

theorem completeness : Completeness (F p) elaborated Assumptions := by
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

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Boolean.And
