import Ragu.Circuits.Element.Add
import Ragu.Instances.Autogen.Element.Add
import Ragu.Core

namespace Ragu.Instances.Element.Add
open Ragu.Instances.Autogen.Element.Add

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Element.Add.Input (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Element.Add.Input
  Output := field

  deserializeInput
  serializeOutput

  Spec input output := output = input.x + input.y

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Element.Add.Input field
      Circuits.Element.Add.circuit

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Add.circuit, Circuits.Element.Add.elaborated, Circuits.Element.Add.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Add.circuit, Circuits.Element.Add.elaborated, Circuits.Element.Add.main]
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.Add.circuit, Circuits.Element.Add.Assumptions,
      Circuits.Element.Add.Spec]
    aesop

end Ragu.Instances.Element.Add
