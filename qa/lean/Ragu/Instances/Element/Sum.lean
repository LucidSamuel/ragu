import Ragu.Circuits.Element.Sum
import Ragu.Instances.Autogen.Element.Sum
import Ragu.Core

namespace Ragu.Instances.Element.Sum
open Ragu.Instances.Autogen.Element.Sum

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Element.Sum.Input (F p) :=
  { x0 := input[0], x1 := input[1], x2 := input[2] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Element.Sum.Input
  Output := field

  deserializeInput
  serializeOutput

  Spec input output := output = input.x0 + input.x1 + input.x2

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Element.Sum.Input field
      Circuits.Element.Sum.circuit

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Sum.circuit, Circuits.Element.Sum.elaborated, Circuits.Element.Sum.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Sum.circuit, Circuits.Element.Sum.elaborated, Circuits.Element.Sum.main]
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.Sum.circuit, Circuits.Element.Sum.Assumptions,
      Circuits.Element.Sum.Spec]
    aesop

end Ragu.Instances.Element.Sum
