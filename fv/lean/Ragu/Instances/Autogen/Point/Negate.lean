import Ragu.Core

namespace Ragu.Instances.Autogen.Point.Negate
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 2

@[reducible]
def outputLen := 2

set_option linter.unusedVariables false in
def exportedOperations (input_var : Var (ProvableVector field inputLen) (F p)) : Operations (F p) := [
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Var (ProvableVector field inputLen) (F p)) : Vector (Expression (F p)) outputLen := #v[
  (input_var.get 0),
  ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 1))
]

end Ragu.Instances.Autogen.Point.Negate
