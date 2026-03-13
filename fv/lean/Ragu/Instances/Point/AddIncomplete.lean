import Ragu.Circuits.Point.AddIncomplete
import Ragu.Core

namespace Ragu.Instances.Point.AddIncomplete
open Core.Primes

@[reducible]
def CircuitField := F Core.Primes.p

def Inputs := ProvableVector field 5

set_option linter.unusedVariables false in
def exported_operations (input_var : Var Inputs CircuitField) : Operations CircuitField := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 0) * (var 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 2)))),
  Operation.assert (((var 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 4)))),
  Operation.assert (((var 1) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * ((input_var.get 2) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 0)))))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 3) * (var 4)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 5)))),
  Operation.assert ((((input_var.get 3) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 1))) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 5)))),
  Operation.assert ((((input_var.get 2) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 0))) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 4)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 6) * (var 7)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 8)))),
  Operation.assert (((var 6) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 3)))),
  Operation.assert (((var 7) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 3)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 9) * (var 10)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 11)))),
  Operation.assert (((var 9) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 3)))),
  Operation.assert (((var 10) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * ((input_var.get 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (((var 8) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 0))) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 2)))))))),
]

set_option linter.unusedVariables false in
@[reducible]
def exported_output (input_var : Var Inputs CircuitField) : List (Expression CircuitField) := [
  (((var 8) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 0))) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 2))),
  ((var 11) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 1))),
  (var 2)
]


def circuit := (Circuits.Point.AddIncomplete.circuit Circuits.Point.Spec.EpAffineParams).main (F:=CircuitField)

def deserializeInput (input : Var Inputs CircuitField) : Var Circuits.Point.AddIncomplete.Inputs CircuitField :=
  {
    P1 := ⟨input.get 0, input.get 1⟩,
    P2 := ⟨input.get 2, input.get 3⟩,
    nonzero := input.get 4
  }


theorem same_circuit (input : Var Inputs CircuitField):
    ((circuit (deserializeInput input)).operations 0).toFlat = (exported_operations input).toFlat := by
  simp [Operations.toFlat, circuit_norm, FormalCircuit.toSubcircuit,
    circuit, deserializeInput, exported_operations,
    Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.elaborated, Circuits.Point.AddIncomplete.main,
    Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
    Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
    Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
    Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  repeat (constructor; rfl)
  constructor


lemma exported_output_len (input : Var Inputs CircuitField) : (exported_output input).length = 3 := by
  simp only [exported_output, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]

theorem same_output (input : Var Inputs CircuitField) :
    ((circuit (deserializeInput input)).output 0).P3.x = (exported_output input)[0] ∧
    ((circuit (deserializeInput input)).output 0).P3.y = (exported_output input)[1] ∧
    ((circuit (deserializeInput input)).output 0).nonzero = (exported_output input)[2] := by
  simp [circuit_norm, FormalCircuit.toSubcircuit,
    circuit, deserializeInput,
    Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.elaborated, Circuits.Point.AddIncomplete.main,
    Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
    Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
    Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
    Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  repeat (constructor <;> congr)


end Ragu.Instances.Point.AddIncomplete
