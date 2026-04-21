import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

/-- Read the allocated element `a` from the prover-supplied hint.
    Takes `(table, idx, slot)` identifying which entry to read. -/
def readElem (hint : ProverHint (F p)) (table : String) (cols : ℕ) (idx slot : ℕ) : F p :=
  let v := (hint table cols).getD idx default
  v[slot]!

def main (table : String) (cols : ℕ) (idx slot : ℕ) (_input : Unit) :
    Circuit (F p) (Var Square (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let a := readElem env.hint table cols idx slot
    (⟨a, a, a * a⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - y)
  return ⟨x, z⟩

def Assumptions (_table : String) (_cols _idx _slot : ℕ)
    (_input : Unit) (_data : ProverData (F p)) (_hint : ProverHint (F p)) := True

def Spec (_input : Unit) (out : Square (F p)) (_data : ProverData (F p)) :=
  out.a_sq = out.a^2

def CompletenessSpec (table : String) (cols : ℕ) (idx slot : ℕ)
    (_input : Unit) (out : Square (F p)) (hint : ProverHint (F p)) :=
  let a := readElem hint table cols idx slot
  out.a = a ∧ out.a_sq = a^2

instance elaborated (table : String) (cols : ℕ) (idx slot : ℕ) :
    ElaboratedCircuit (F p) unit Square where
  main := main table cols idx slot
  localLength _ := 3

theorem soundness (table : String) (cols : ℕ) (idx slot : ℕ) :
    GeneralFormalCircuit.Soundness (F p) (elaborated table cols idx slot) Spec := by
  circuit_proof_start
  obtain ⟨c1, c2⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2
  rw [←c1, c2]
  ring

theorem completeness (table : String) (cols : ℕ) (idx slot : ℕ) :
    GeneralFormalCircuit.Completeness (F p) (elaborated table cols idx slot)
      (Assumptions table cols idx slot) := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  refine ⟨?_, ?_⟩ <;> ring

theorem completenessSpec (table : String) (cols : ℕ) (idx slot : ℕ) :
    GeneralFormalCircuit.CompletenessSpecProof (F p) (elaborated table cols idx slot)
      (Assumptions table cols idx slot) (CompletenessSpec table cols idx slot) := by
  circuit_proof_start [CompletenessSpec]
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero, Nat.reduceAdd, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  refine ⟨h0, ?_⟩
  rw [h2]; ring

def generalCircuit (table : String) (cols : ℕ) (idx slot : ℕ) :
    GeneralFormalCircuit (F p) unit Square :=
  { elaborated table cols idx slot with
    Assumptions := Assumptions table cols idx slot,
    Spec,
    CompletenessSpec := CompletenessSpec table cols idx slot,
    soundness := soundness table cols idx slot,
    completeness := completeness table cols idx slot,
    completenessSpec := completenessSpec table cols idx slot }

end Ragu.Circuits.Element.AllocSquare
