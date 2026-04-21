import Ragu.Circuits.Point.Constant
import Ragu.Instances.Autogen.Point.Constant
import Ragu.Core

namespace Ragu.Instances.Point.Constant
open Ragu.Instances.Autogen.Point.Constant

/-- Coordinates of the Pallas generator (matching the value the Rust harness
passes via `EpAffine::generator()`). These constants must stay in sync with
`qa/crates/lean_extraction/src/instances/point_constant.rs`. -/
def px : F p := 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000
def py : F p := 2

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var unit (F p) := ()

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[output.x, output.y]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := unit
  Output := Circuits.Point.Spec.Point

  deserializeInput
  serializeOutput

  Spec (_input : Unit) (output : Circuits.Point.Spec.Point (F p)) :=
    output.x = px ∧ output.y = py

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) unit Circuits.Point.Spec.Point
      (Circuits.Point.Constant.circuit px py)

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Point.Constant.circuit, Circuits.Point.Constant.elaborated, Circuits.Point.Constant.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      px, py,
      Circuits.Point.Constant.circuit, Circuits.Point.Constant.elaborated, Circuits.Point.Constant.main]
    refine ⟨?_, ?_⟩ <;> rfl
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Point.Constant.circuit, Circuits.Point.Constant.Assumptions,
      Circuits.Point.Constant.Spec]
    aesop

end Ragu.Instances.Point.Constant
