import Ragu.Circuits.Element.Square
import Ragu.Instances.Autogen.Element.Square
import Ragu.Core

namespace Ragu.Instances.Element.Square
open Ragu.Instances.Autogen.Element.Square

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

  Spec input output := output = input^2

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) field field
      Circuits.Element.Square.circuit

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm, exportedOperations,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.Square.circuit, Circuits.Element.Square.Assumptions,
      Circuits.Element.Square.Spec]
    rfl

end Ragu.Instances.Element.Square
