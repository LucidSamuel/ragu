import Clean.Circuit
import Ragu.Circuits.Point.Alloc
import Ragu.Core

namespace Ragu.Instances.Point.Alloc
open Core.Primes

@[reducible]
def CircuitField := F Core.Primes.p

def operations : Operations CircuitField := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 0) * (var 1)) + (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 * (var 2)))),
  Operation.assert (((var 0) + (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 * (var 1)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 3) * (var 4)) + (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 * (var 5)))),
  Operation.assert (((var 3) + (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 * (var 0)))),
  Operation.assert (((var 4) + (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 * (var 2)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 6) * (var 7)) + (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 * (var 8)))),
  Operation.assert (((var 6) + (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 * (var 7)))),
  Operation.assert ((((var 5) + (0x0000000000000000000000000000000000000000000000000000000000000005 * 1)) + (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 * (var 8)))),
]

def circuit := Circuits.Point.Alloc.circuit.main (F:=CircuitField) default


theorem same_circuit : (circuit.operations 0).toFlat = operations.toFlat :=  by
  simp [Operations.toFlat, circuit_norm, FormalCircuit.toSubcircuit,
    circuit,
    Circuits.Point.Alloc.circuit, Circuits.Point.Alloc.elaborated, Circuits.Point.Alloc.main,
    Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
    Circuits.Element.AllocSquare.circuit, Circuits.Element.AllocSquare.elaborated, Circuits.Element.AllocSquare.main,
    Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  rfl

end Ragu.Instances.Point.Alloc
