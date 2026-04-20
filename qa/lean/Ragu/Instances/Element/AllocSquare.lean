import Ragu.Circuits.Element.AllocSquare
import Ragu.Instances.Autogen.Element.AllocSquare
import Ragu.Core

namespace Ragu.Instances.Element.AllocSquare
open Ragu.Instances.Autogen.Element.AllocSquare

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var unit (F p) := ()

def serializeOutput (output : Var Circuits.Element.AllocSquare.Square (F p)) : Vector (Expression (F p)) 2 :=
  #v[output.a, output.a_sq]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := unit
  Output := Circuits.Element.AllocSquare.Square

  deserializeInput
  serializeOutput

  Spec _input output := output.a_sq = output.a^2

  reimplementation := Circuits.Element.AllocSquare.generalCircuit (fun _ => 0)

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm, exportedOperations,
      GeneralFormalCircuit.toSubcircuit,
      Circuits.Element.AllocSquare.generalCircuit,
      Circuits.Element.AllocSquare.elaborated,
      Circuits.Element.AllocSquare.main]
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.AllocSquare.generalCircuit,
      Circuits.Element.AllocSquare.elaborated,
      Circuits.Element.AllocSquare.main]
  same_spec := by
    intro input output
    dsimp only [Circuits.Element.AllocSquare.generalCircuit,
      Circuits.Element.AllocSquare.Spec]
    rfl

end Ragu.Instances.Element.AllocSquare
