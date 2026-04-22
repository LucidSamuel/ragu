import Clean.Circuit

namespace Ragu.Circuits.Boolean.Multipack
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  b0 : F
  b1 : F
  b2 : F
deriving ProvableStruct

/-- `multipack` is variadic; this extraction fixes length 3 as a
representative case. Since `F::CAPACITY = 254`, all three bits fit in a
single chunk, so the output is a single packed `Element`. The underlying
`dr.add` accumulator is virtual (no gates or constraints emitted) and
produces the LE-packed linear combination `b0 + 2·b1 + 4·b2`.

The FV guarantee here is specifically for the single-chunk path
(bit length ≤ `F::CAPACITY`). Production `multipack` calls with
more bits split across multiple field elements via `chunks(capacity)`;
the per-chunk shape is identical to this instance but that general
iteration pattern is not exercised by this extraction. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  return input.b0 + 2 * input.b1 + 4 * input.b2

/-- Caller must promise all three inputs are boolean; otherwise the
algebraic `Spec` still holds, but the output is no longer the unsigned
integer interpretation of the bits. -/
def Assumptions (input : Input (F p)) :=
  (input.b0 = 0 ∨ input.b0 = 1) ∧
  (input.b1 = 0 ∨ input.b1 = 1) ∧
  (input.b2 = 0 ∨ input.b2 = 1)

/-- The output is the little-endian packing: `b0 + 2·b1 + 4·b2`. -/
def Spec (input : Input (F p)) (out : F p) :=
  out = input.b0 + 2 * input.b1 + 4 * input.b2

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 0

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Boolean.Multipack
