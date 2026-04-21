import Clean.Circuit

namespace Ragu.Circuits.Element.Sum
variable {p : ℕ} [Fact p.Prime]

/-- `Element::sum` is variadic (`IntoIterator<Item = Element>`). This
extraction instance fixes length 3 as a representative choice; a
length-polymorphic reimpl would require dependent-type machinery that
Clean doesn't currently expose. For other lengths, add analogous
FormalInstances that mirror this structure. -/
structure Input (F : Type) where
  x0 : F
  x1 : F
  x2 : F
deriving ProvableStruct

def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  -- Mirrors the production left-associative fold starting from
  -- `Element::zero(dr) = dr.constant(Coeff::Zero)`. Using
  -- `Expression.const 0` explicitly matches the autogen's rendering.
  return (Expression.const 0) + input.x0 + input.x1 + input.x2

def Assumptions (_input : Input (F p)) := True

def Spec (input : Input (F p)) (output : F p) :=
  output = input.x0 + input.x1 + input.x2

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 0

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  ring

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.Sum
