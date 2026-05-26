import Ragu.Circuits.NonzeroBank.ScopeK2
import Ragu.Instances.Autogen.NonzeroBank.ScopeK2
import Ragu.Core

namespace Ragu.Instances.NonzeroBank.ScopeK2
open Ragu.Instances.Autogen.NonzeroBank.ScopeK2

def deserializeInput (input : Vector (Expression (F p)) inputLen) :
    Var Circuits.NonzeroBank.ScopeK2.Input (F p) :=
  { f1 := input[0], f2 := input[1], inverse := fun _ => 0 }

def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.NonzeroBank.ScopeK2.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.NonzeroBank.ScopeK2.circuit,
      Circuits.NonzeroBank.ScopeK2.elaborated,
      Circuits.NonzeroBank.ScopeK2.main,
      Circuits.Element.Mul.circuit,
      Circuits.Element.Mul.elaborated,
      Circuits.Element.Mul.main,
      Circuits.Element.EnforceNonzero.circuit,
      Circuits.Element.EnforceNonzero.elaborated,
      Circuits.Element.EnforceNonzero.main,
      Circuits.Core.Mul.main]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  same_output := by
    intro input
    rfl

end Ragu.Instances.NonzeroBank.ScopeK2
