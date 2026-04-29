import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- Under the `()` allocator, `Element::alloc` calls `Allocator::alloc`,
which emits a full 3-wire gate but returns the first wire — the other
two are discarded. The returned wire is unconstrained (there always
exist `b`, `c` satisfying `a · b = c` for any `a`, e.g. `b = c = 0`). -/
def main (hint : ProverEnvironment (F p) → Row (F p))
    : Circuit (F p) (Expression (F p)) := do
  let ⟨a, _, _⟩ ← Core.AllocMul.circuit hint
  return a

/-- The output is unconstrained from the verifier's perspective — any value
can be part of a valid `(a, b, c)` triple with `a · b = c` (e.g. take
`a = c = 0`). The useful content is the allocation itself. -/
def Spec (_input : Unit) (_out : F p) (_data : ProverData (F p)) := True

def ProverSpec (input : Row (F p)) (out : F p) (_ : ProverHint (F p)) :=
  out = input.x

instance elaborated : ElaboratedCircuit (F p) (UnconstrainedDep Core.AllocMul.Row) field where
  main
  output _ offset := varFromOffset field offset
  localLength _ := 3

theorem soundness
    : GeneralFormalCircuit.WithHint.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start

theorem completeness : GeneralFormalCircuit.WithHint.Completeness (F p) elaborated
    (fun _ _ _ => True) ProverSpec := by
  circuit_proof_start [Core.AllocMul.circuit, Core.AllocMul.ProverSpec]
  grind

def circuit : GeneralFormalCircuit.WithHint (F p) (UnconstrainedDep Core.AllocMul.Row) field :=
  { elaborated with Spec, ProverSpec, soundness, completeness }

end Ragu.Circuits.Element.Alloc
