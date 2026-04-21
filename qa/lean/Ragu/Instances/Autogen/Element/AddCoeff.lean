import Ragu.Core

namespace Ragu.Instances.Autogen.Element.AddCoeff
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 2

@[reducible]
def outputLen := 1

set_option linter.unusedVariables false in
def exportedOperations (input_var : Vector (Expression (F p)) inputLen) : Operations (F p) := [
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Vector (Expression (F p)) inputLen) : Vector (Expression (F p)) outputLen := #v[
  ((input_var[0]) + ((0x0000000000000000000000000000000000000000000000000000000000000007 : Expression (F p)) * (input_var[1])))
]

end Ragu.Instances.Autogen.Element.AddCoeff
