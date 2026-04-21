import Ragu.Circuits.Boolean.And
import Ragu.Instances.Autogen.Boolean.And
import Ragu.Core

namespace Ragu.Instances.Boolean.And
open Ragu.Instances.Autogen.Boolean.And

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Boolean.And.Input (F p) :=
  { a := input[0], b := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Boolean.And.Input
  Output := field

  Spec (input : Circuits.Boolean.And.Input (F p)) (output : F p) :=
    (input.a = 0 ∨ input.a = 1) ∧ (input.b = 0 ∨ input.b = 1)
      → output = input.a * input.b

  deserializeInput
  serializeOutput

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Boolean.And.Input field
      Circuits.Boolean.And.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Boolean.And.circuit,
      Circuits.Boolean.And.elaborated,
      Circuits.Boolean.And.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Boolean.And.circuit,
      Circuits.Boolean.And.elaborated,
      Circuits.Boolean.And.main]
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Boolean.And.circuit,
      Circuits.Boolean.And.Assumptions,
      Circuits.Boolean.And.Spec]
    aesop

end Ragu.Instances.Boolean.And
