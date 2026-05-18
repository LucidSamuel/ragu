import Clean.Circuit
import Clean.Circuit.Loops
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Element.EnforceRootOfUnity
variable {p : ℕ} [Fact p.Prime]

/-- `Element::enforce_root_of_unity(k)` enforces `self ^ (2^k) = 1` by
squaring `k` times. This Lean reimpl is polymorphic on `k : ℕ`, mirroring
the Rust gadget's full generality (parameter `k : u32` in
`crates/ragu_primitives/src/element.rs::enforce_root_of_unity`).

Modeled as a `FormalAssertion`: the gadget is constraint-only (no
output), `Spec` acts as both assumption for completeness and conclusion
for soundness.

The body iteratively squares the input via `squareIter`, matching the
Rust `for _ in 0..k { value = value.square(dr)?; }` loop. -/
def squareIter : (k : ℕ) → Expression (F p) → Circuit (F p) (Expression (F p))
  | 0, x => pure x
  | k+1, x => do
    let sq ← Mul.circuit ⟨x, x⟩
    squareIter k sq

def main (k : ℕ) (input : Expression (F p)) : Circuit (F p) (Var unit (F p)) := do
  let final ← squareIter k input
  assertZero (final - 1)

def Assumptions (_ : F p) := True

/-- The verifier learns `input ^ (2^k) = 1`. -/
def Spec (k : ℕ) (input : F p) :=
  input ^ (2 ^ k) = 1

/-- `squareIter k x` has local length `3 * k` (one `Mul.circuit` of length
3 per iteration), for any input `x` and any starting offset `n`. -/
private lemma squareIter_localLength (k : ℕ) (x : Expression (F p)) (n : ℕ) :
    Operations.localLength (squareIter k x n).2 = 3 * k := by
  induction k generalizing x n with
  | zero => rfl
  | succ k ih =>
    simp only [squareIter, Circuit.bind_def, circuit_norm, Mul.circuit, Mul.elaborated]
    rw [ih]
    ring

/-- `squareIter k x` produces subcircuit-consistent operations for any
input and any starting offset. -/
private lemma squareIter_subcircuitsConsistent (k : ℕ) (x : Expression (F p)) (n : ℕ) :
    Operations.forAll n
      { subcircuit := fun offset {m} _ => m = offset }
      (squareIter k x n).2 := by
  induction k generalizing x n with
  | zero => simp [squareIter, circuit_norm]
  | succ k ih =>
    simp only [squareIter, Circuit.bind_def, circuit_norm, Mul.circuit, Mul.elaborated]
    rw [show (3 + n : ℕ) = n + 3 from Nat.add_comm 3 n]
    exact ih (var ⟨n + 2⟩) (n + 3)

instance elaborated (k : ℕ) : ElaboratedCircuit (F p) field unit where
  main := main k
  localLength _ := 3 * k
  localLength_eq input offset := by
    show Operations.localLength (main k input offset).2 = 3 * k
    simp only [main, Circuit.bind_def]
    show Operations.localLength
      (((squareIter k input).bind (fun final => assertZero (final - 1))) offset).2 = 3 * k
    simp only [Circuit.bind_def, circuit_norm]
    exact squareIter_localLength k input offset
  subcircuitsConsistent input offset := by
    simp only [main, Circuit.bind_def, circuit_norm]
    exact squareIter_subcircuitsConsistent k input offset

/-- The output of `squareIter k x_var` evaluates to `x_val ^ (2^k)`,
provided the constraints emitted by `squareIter` are satisfied and the
input expression evaluates to `x_val`. Proved by induction on `k`,
delegating each step's product equality to `Mul.Spec`. -/
private lemma squareIter_eval_correct (k : ℕ) :
    ∀ (env : Environment (F p)) (x_var : Expression (F p)) (x_val : F p) (n : ℕ),
      Expression.eval env x_var = x_val →
      Circuit.ConstraintsHold.Soundness env (squareIter k x_var n).2 →
      Expression.eval env (squareIter k x_var n).1 = x_val ^ (2 ^ k) := by
  induction k with
  | zero =>
    intros env x_var x_val n h_eval _
    simp [squareIter]
    exact h_eval
  | succ k ih =>
    intros env x_var x_val n h_eval h_sound
    simp only [squareIter, Circuit.bind_def, circuit_norm,
      Mul.circuit, Mul.Assumptions, Mul.Spec, Mul.elaborated] at h_sound ⊢
    obtain ⟨h_mul, h_rest⟩ := h_sound
    -- h_mul : env.get (n+2) = eval x_var * eval x_var, i.e. wire = x_val^2
    -- h_rest : ConstraintsHold over squareIter k at offset n+3, with the wire as input
    have h_sq_eval : Expression.eval env (var ⟨n + 2⟩) = x_val * x_val := by
      simp [Expression.eval, h_mul, h_eval]
    rw [ih env (var ⟨n + 2⟩) (x_val * x_val) (n + 3) h_sq_eval h_rest]
    ring

theorem soundness (k : ℕ) :
    FormalAssertion.Soundness (F p) (elaborated k) Assumptions (Spec k) := by
  circuit_proof_start [Mul.circuit, Mul.Assumptions, Mul.Spec]
  obtain ⟨h_sound, h_final⟩ := h_holds
  have h_out := squareIter_eval_correct k env input_var input i₀ h_input h_sound
  rw [add_neg_eq_zero] at h_final
  rw [h_out] at h_final
  exact h_final

/-- Companion to `squareIter_eval_correct` for the completeness side:
given that the prover environment uses the canonical local witnesses for
`squareIter k x_var`, the Mul constraints all hold by construction and
the output evaluates to `x_val ^ (2^k)`. -/
private lemma squareIter_completeness (k : ℕ) :
    ∀ (env : ProverEnvironment (F p)) (x_var : Expression (F p)) (x_val : F p) (n : ℕ),
      Expression.eval env.toEnvironment x_var = x_val →
      env.UsesLocalWitnessesCompleteness n (squareIter k x_var n).2 →
      Circuit.ConstraintsHold.Completeness env (squareIter k x_var n).2 ∧
        Expression.eval env.toEnvironment (squareIter k x_var n).1 = x_val ^ (2 ^ k) := by
  induction k with
  | zero =>
    intros env x_var x_val n h_eval _
    refine ⟨?_, ?_⟩
    · simp [squareIter, circuit_norm]
    · simp [squareIter]; exact h_eval
  | succ k ih =>
    intros env x_var x_val n h_eval h_env
    simp only [squareIter, Circuit.bind_def, circuit_norm,
      Mul.circuit, Mul.Assumptions, Mul.Spec, Mul.elaborated] at h_env ⊢
    obtain ⟨h_wit, h_rest⟩ := h_env
    -- h_wit : env.get (n+2) = eval x_var * eval x_var (the canonical Mul witness)
    -- h_rest : UsesLocalWitnessesCompleteness for squareIter k at offset n+3
    have h_sq_eval : Expression.eval env.toEnvironment (var ⟨n + 2⟩) = x_val * x_val := by
      simp [Expression.eval, h_wit, h_eval]
    obtain ⟨h_inner_constr, h_inner_eval⟩ :=
      ih env (var ⟨n + 2⟩) (x_val * x_val) (n + 3) h_sq_eval h_rest
    refine ⟨h_inner_constr, ?_⟩
    rw [h_inner_eval]
    ring

theorem completeness (k : ℕ) :
    FormalAssertion.Completeness (F p) (elaborated k) Assumptions (Spec k) := by
  circuit_proof_start [Mul.circuit, Mul.Assumptions, Mul.Spec]
  obtain ⟨h_constr, h_out⟩ := squareIter_completeness k env input_var input i₀ h_input h_env
  refine ⟨h_constr, ?_⟩
  rw [h_out, h_spec]
  ring

def circuit (k : ℕ) : FormalAssertion (F p) field :=
  { elaborated k with
    Assumptions
    Spec := Spec k
    soundness := soundness k
    completeness := completeness k }

end Ragu.Circuits.Element.EnforceRootOfUnity
