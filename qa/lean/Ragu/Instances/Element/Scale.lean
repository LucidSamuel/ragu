import Ragu.Circuits.Element.Scale
import Ragu.Instances.Autogen.Element.Scale
import Ragu.Core

namespace Ragu.Instances.Element.Scale
open Ragu.Instances.Autogen.Element.Scale

/-- Coefficient chosen for this extraction instance. Must match the `Coeff`
value used in `qa/crates/lean_extraction/src/instances/element_scale.rs`. -/
def coeff : F p := 5

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

  Spec (input : F p) (output : F p) := output = coeff * input

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) field field
      (Circuits.Element.Scale.circuit coeff)

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Scale.circuit, Circuits.Element.Scale.elaborated, Circuits.Element.Scale.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Scale.circuit, Circuits.Element.Scale.elaborated, Circuits.Element.Scale.main]
    show Expression.mul _ _ = Expression.mul _ _
    congr 1
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.Scale.circuit, Circuits.Element.Scale.Assumptions,
      Circuits.Element.Scale.Spec]
    aesop

end Ragu.Instances.Element.Scale
