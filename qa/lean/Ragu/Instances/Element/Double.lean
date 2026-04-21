import Ragu.Circuits.Element.Double
import Ragu.Instances.Autogen.Element.Double
import Ragu.Core

namespace Ragu.Instances.Element.Double
open Ragu.Instances.Autogen.Element.Double

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

  deserializeInput
  serializeOutput

  Spec (input : F p) (output : F p) := output = input + input

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) field field
      Circuits.Element.Double.circuit

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Double.circuit, Circuits.Element.Double.elaborated, Circuits.Element.Double.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Double.circuit, Circuits.Element.Double.elaborated, Circuits.Element.Double.main]
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.Double.circuit, Circuits.Element.Double.Assumptions,
      Circuits.Element.Double.Spec]
    aesop

end Ragu.Instances.Element.Double
