import Clean.Circuit

namespace Ragu.Circuits.Core.AllocMul
variable {p : ℕ} [Fact p.Prime]

structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

/-- Read the `(x, y)` pair the honest prover has allocated at index `idx`
    of the `"alloc_mul_w"` witness table. `z` is computed as `x * y`. -/
def readRow (hint : ProverHint (F p)) (idx : ℕ) : Row (F p) :=
  let v := (hint "alloc_mul_w" 2).getD idx default
  ⟨v[0], v[1], v[0] * v[1]⟩

def main (idx : ℕ) (_input : Unit) : Circuit (F p) (Var Row (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let r := readRow env.hint idx
    (⟨r.x, r.y, r.x * r.y⟩ : Row (F p))
    : Circuit (F p) (Var Row (F p)))
  assertZero (x * y - z)
  return ⟨x, y, z⟩

def Assumptions (_idx : ℕ) (_input : Unit) (_data : ProverData (F p)) (_hint : ProverHint (F p)) := True

def Spec (_input : Unit) (out : Row (F p)) (_data : ProverData (F p)) :=
  out.x * out.y = out.z

/-- The output row equals the `readRow` of the hint at `idx`. -/
def CompletenessSpec (idx : ℕ) (_input : Unit) (out : Row (F p)) (hint : ProverHint (F p)) :=
  let r := readRow hint idx
  out.x = r.x ∧ out.y = r.y ∧ out.z = r.x * r.y

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) unit Row where
  main := main idx
  localLength _ := 3

theorem soundness (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) Spec := by
  circuit_proof_start
  rw [add_neg_eq_zero] at h_holds
  exact h_holds

theorem completeness (idx : ℕ) :
    GeneralFormalCircuit.Completeness (F p) (elaborated idx) (Assumptions idx) := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  ring

theorem completenessSpec (idx : ℕ) :
    GeneralFormalCircuit.CompletenessSpecProof (F p) (elaborated idx)
      (Assumptions idx) (CompletenessSpec idx) := by
  circuit_proof_start [CompletenessSpec]
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  exact ⟨h0, h1, h2⟩

def circuit (idx : ℕ) : GeneralFormalCircuit (F p) unit Row :=
  { elaborated idx with
    Assumptions := Assumptions idx,
    Spec,
    CompletenessSpec := CompletenessSpec idx,
    soundness := soundness idx,
    completeness := completeness idx,
    completenessSpec := completenessSpec idx }

end Ragu.Circuits.Core.AllocMul
