import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

/-- Read one field element from ProverData; used as both x and y in the squaring witness. -/
def readInput (data : ProverData (F p)) (idx : ℕ) : F p :=
  ((data "alloc_square_w" 1).getD idx default)[0]

def main (idx : ℕ) (_input : Unit) : Circuit (F p) (Var Square (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let a := readInput env.data idx
    (⟨a, a, a * a⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - y)
  return ⟨x, z⟩

def Assumptions (_idx : ℕ) (_input : Unit) (_data : ProverData (F p)) := True

def Spec (_input : Unit) (out : Square (F p)) (_data : ProverData (F p)) :=
  out.a_sq = out.a^2

def CompletenessSpec (idx : ℕ) (_input : Unit) (out : Square (F p)) (data : ProverData (F p)) :=
  out.a = readInput data idx ∧ out.a_sq = (readInput data idx)^2

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) unit Square where
  main := main idx
  localLength _ := 3

theorem soundness (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) Spec := by
  circuit_proof_start
  obtain ⟨c1, c2⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2
  rw [←c1, c2]
  ring

theorem completeness (idx : ℕ) : GeneralFormalCircuit.Completeness (F p) (elaborated idx) (Assumptions idx) := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, readInput, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  refine ⟨?_, ?_⟩ <;> ring

theorem completenessSpec (idx : ℕ) : GeneralFormalCircuit.CompletenessSpecProof (F p) (elaborated idx) (Assumptions idx) (CompletenessSpec idx) := by
  circuit_proof_start [CompletenessSpec, readInput]
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero, Nat.reduceAdd, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  constructor
  · rw [h0]; simp
  · rw [h2]; simp; ring

def generalCircuit (idx : ℕ) : GeneralFormalCircuit (F p) unit Square :=
  { elaborated idx with
    Assumptions := Assumptions idx,
    Spec := Spec,
    CompletenessSpec := CompletenessSpec idx,
    soundness := soundness idx,
    completeness := completeness idx,
    completenessSpec := completenessSpec idx }

end Ragu.Circuits.Element.AllocSquare
