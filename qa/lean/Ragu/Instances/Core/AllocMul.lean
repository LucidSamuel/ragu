import Ragu.Circuits.Core.AllocMul
import Ragu.Instances.Autogen.Core.AllocMul
import Ragu.Core

namespace Ragu.Instances.Core.AllocMul
open Ragu.Instances.Autogen.Core.AllocMul

def deserializeInput (_ : Vector (Expression (F p)) inputLen) :
    Var (UnconstrainedDep Circuits.Core.AllocMul.Row) (F p) :=
  default

def serializeOutput (output : Var Circuits.Core.AllocMul.Row (F p)) : Vector (Expression (F p)) 3 :=
  #v[output.x, output.y, output.z]

def formal_instance : Core.Statements.GeneralFormalWithHintInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Core.AllocMul.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.main]
    rfl
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.main]

end Ragu.Instances.Core.AllocMul
