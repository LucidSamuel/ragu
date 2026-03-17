import Clean.Circuit

namespace Ragu.Circuits.Core.AllocMul
variable {p : ℕ} [Fact p.Prime]

structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

/-- Read the witness row from ProverData at the given index. Only x and y are read;
    z = x * y is computed. -/
def readRow (data : ProverData (F p)) (idx : ℕ) : Row (F p) :=
  let v := (data "alloc_mul_w" 2).getD idx default
  ⟨v[0], v[1], v[0] * v[1]⟩

end Ragu.Circuits.Core.AllocMul
