import Ragu.Circuits.Boolean.IsZero
import Ragu.Instances.Autogen.Boolean.IsZero
import Ragu.Core

namespace Ragu.Instances.Boolean.IsZero
open Ragu.Instances.Autogen.Boolean.IsZero

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var field (F p) :=
  input[0]

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := field
  Output := field

  Spec (input : F p) (output : F p) :=
    output = if input = 0 then 1 else 0

  deserializeInput
  serializeOutput

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) field field
      Circuits.Boolean.IsZero.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Boolean.IsZero.circuit,
      Circuits.Boolean.IsZero.elaborated,
      Circuits.Boolean.IsZero.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Boolean.IsZero.circuit,
      Circuits.Boolean.IsZero.elaborated,
      Circuits.Boolean.IsZero.main]
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Boolean.IsZero.circuit,
      Circuits.Boolean.IsZero.Assumptions,
      Circuits.Boolean.IsZero.Spec]
    aesop

end Ragu.Instances.Boolean.IsZero
