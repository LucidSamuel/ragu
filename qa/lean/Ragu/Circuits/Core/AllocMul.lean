import Clean.Circuit

namespace Ragu.Circuits.Core.AllocMul
variable {p : ℕ} [Fact p.Prime]

structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

/-- Read the `(x, y)` pair the honest prover has allocated at index `idx`
    of the `"alloc_mul_w"` witness table. `z` is computed as `x * y`.
    One convenient `hintReader` a caller can pass into `circuit`; callers
    are free to build other `ProverHint → Row` readers. -/
def readRow (hint : ProverHint (F p)) (idx : ℕ) : Row (F p) :=
  let v := (hint "alloc_mul_w" 2).getD idx default
  ⟨v[0], v[1], v[0] * v[1]⟩

def main (hintReader : ProverHint (F p) → Row (F p)) (_input : Unit) : Circuit (F p) (Var Row (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let r := hintReader env.hint
    (⟨r.x, r.y, r.x * r.y⟩ : Row (F p))
    : Circuit (F p) (Var Row (F p)))
  assertZero (x * y - z)
  return ⟨x, y, z⟩

def Assumptions (_hintReader : ProverHint (F p) → Row (F p))
    (_input : Unit) (_data : ProverData (F p)) (_hint : ProverHint (F p)) := True

def Spec (_input : Unit) (out : Row (F p)) (_data : ProverData (F p)) :=
  out.x * out.y = out.z

/-- The output row equals `hintReader` applied to the runtime hint. -/
def CompletenessSpec (hintReader : ProverHint (F p) → Row (F p))
    (_input : Unit) (out : Row (F p)) (hint : ProverHint (F p)) :=
  let r := hintReader hint
  out.x = r.x ∧ out.y = r.y ∧ out.z = r.x * r.y

instance elaborated (hintReader : ProverHint (F p) → Row (F p)) : ElaboratedCircuit (F p) unit Row where
  main := main hintReader
  localLength _ := 3

theorem soundness (hintReader : ProverHint (F p) → Row (F p)) :
    GeneralFormalCircuit.Soundness (F p) (elaborated hintReader) Spec := by
  circuit_proof_start
  rw [add_neg_eq_zero] at h_holds
  exact h_holds

theorem completeness (hintReader : ProverHint (F p) → Row (F p)) :
    GeneralFormalCircuit.Completeness (F p) (elaborated hintReader) (Assumptions hintReader) := by
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

theorem completenessSpec (hintReader : ProverHint (F p) → Row (F p)) :
    GeneralFormalCircuit.CompletenessSpecProof (F p) (elaborated hintReader)
      (Assumptions hintReader) (CompletenessSpec hintReader) := by
  circuit_proof_start [CompletenessSpec]
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  exact ⟨h0, h1, h2⟩

def circuit (hintReader : ProverHint (F p) → Row (F p)) : GeneralFormalCircuit (F p) unit Row :=
  { elaborated hintReader with
    Assumptions := Assumptions hintReader,
    Spec,
    CompletenessSpec := CompletenessSpec hintReader,
    soundness := soundness hintReader,
    completeness := completeness hintReader,
    completenessSpec := completenessSpec hintReader }

end Ragu.Circuits.Core.AllocMul
