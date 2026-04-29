import Ragu.Circuits.Element.DivNonzero
import Ragu.Instances.Autogen.Element.DivNonzero
import Ragu.Core

namespace Ragu.Instances.Element.DivNonzero
open Ragu.Instances.Autogen.Element.DivNonzero

def deserializeInput (input : Vector (Expression (F p)) inputLen) :
    Var Circuits.Element.DivNonzero.Input (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.DivNonzero.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.DivNonzero.circuit,
      Circuits.Element.DivNonzero.elaborated,
      Circuits.Element.DivNonzero.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated]
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.DivNonzero.circuit,
      Circuits.Element.DivNonzero.elaborated,
      Circuits.Element.DivNonzero.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated]

end Ragu.Instances.Element.DivNonzero
