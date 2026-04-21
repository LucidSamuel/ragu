import Ragu.Core

namespace Ragu.Instances.Autogen.Point.Constant
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 0

@[reducible]
def outputLen := 2

set_option linter.unusedVariables false in
def exportedOperations (input_var : Vector (Expression (F p)) inputLen) : Operations (F p) := [
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Vector (Expression (F p)) inputLen) : Vector (Expression (F p)) outputLen := #v[
  (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)),
  (0x0000000000000000000000000000000000000000000000000000000000000002 : Expression (F p))
]

end Ragu.Instances.Autogen.Point.Constant
