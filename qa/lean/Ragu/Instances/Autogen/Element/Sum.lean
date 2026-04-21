import Ragu.Core

namespace Ragu.Instances.Autogen.Element.Sum
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 3

@[reducible]
def outputLen := 1

set_option linter.unusedVariables false in
def exportedOperations (input_var : Vector (Expression (F p)) inputLen) : Operations (F p) := [
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Vector (Expression (F p)) inputLen) : Vector (Expression (F p)) outputLen := #v[
  (((((0 : F p) : Expression (F p)) + (input_var[0])) + (input_var[1])) + (input_var[2]))
]

end Ragu.Instances.Autogen.Element.Sum
