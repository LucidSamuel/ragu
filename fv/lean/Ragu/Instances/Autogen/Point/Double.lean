import Ragu.Core

namespace Ragu.Instances.Autogen.Point.Double
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 2

@[reducible]
def outputLen := 2

set_option linter.unusedVariables false in
def exportedOperations (input_var : Var (ProvableVector field inputLen) (F p)) : Operations (F p) := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 0) * (var 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 2)))),
  Operation.assert (((var 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 0)))),
  Operation.assert (((var 1) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 0)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 3) * (var 4)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 5)))),
  Operation.assert ((((0x0000000000000000000000000000000000000000000000000000000000000003 : Expression (F p)) * (var 2)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 5)))),
  Operation.assert ((((input_var.get 1) + (input_var.get 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 4)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 6) * (var 7)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 8)))),
  Operation.assert (((var 6) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 3)))),
  Operation.assert (((var 7) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 3)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 9) * (var 10)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 11)))),
  Operation.assert (((var 9) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 3)))),
  Operation.assert (((var 10) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * ((input_var.get 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * ((var 8) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * ((input_var.get 0) + (input_var.get 0))))))))),
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Var (ProvableVector field inputLen) (F p)) : Vector (Expression (F p)) outputLen := #v[
  ((var 8) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * ((input_var.get 0) + (input_var.get 0)))),
  ((var 11) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 1)))
]

end Ragu.Instances.Autogen.Point.Double
