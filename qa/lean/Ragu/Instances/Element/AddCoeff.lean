import Ragu.Circuits.Element.AddCoeff
import Ragu.Instances.Autogen.Element.AddCoeff
import Ragu.Core

namespace Ragu.Instances.Element.AddCoeff
open Ragu.Instances.Autogen.Element.AddCoeff

/-- Coefficient chosen for this extraction instance. Must match the `Coeff`
value used in `qa/crates/lean_extraction/src/instances/element_add_coeff.rs`. -/
def coeff : F p := 7

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Element.AddCoeff.Input (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Element.AddCoeff.Input
  Output := field

  deserializeInput
  serializeOutput

  Spec input output := output = input.x + coeff * input.y

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Element.AddCoeff.Input field
      (Circuits.Element.AddCoeff.circuit coeff)

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.AddCoeff.circuit, Circuits.Element.AddCoeff.elaborated, Circuits.Element.AddCoeff.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.AddCoeff.circuit, Circuits.Element.AddCoeff.elaborated, Circuits.Element.AddCoeff.main]
    show Expression.add _ (Expression.mul _ _) = Expression.add _ (Expression.mul _ _)
    congr 2
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.AddCoeff.circuit, Circuits.Element.AddCoeff.Assumptions,
      Circuits.Element.AddCoeff.Spec]
    aesop

end Ragu.Instances.Element.AddCoeff
