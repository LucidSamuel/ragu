# Expressions and environment

Circuits in Clean are written symbolically. The basic objects are `Variable`, `Expression`, and `Environment`.

## Variables

At the lowest level, a variable is just an index, pointing to a particular position in the environment.

```lean
structure Variable (F : Type) where
  index : ℕ
```

Expressions are then defined as follows:

```lean
inductive Expression (F : Type) where
  | var : Variable F -> Expression F
  | const : F -> Expression F
  | add : Expression F -> Expression F -> Expression F
  | mul : Expression F -> Expression F -> Expression F
```

Expressions can be built from:
- variables, which are references to environment values,
- constant field elements,
- addition of two expressions,
- multiplication of two expressions.

Clean equips `Expression F` with the usual arithmetic notation, so circuit code can write expressions such as:

```lean
x * y - z
```

instead of manually using constructors like `Expression.mul` and `Expression.add`.

## Environment

An environment provides concrete values for variables:

```lean
structure Environment (F : Type) where
  get : ℕ → F
  data : ProverData F
```

- `get` is a function that assigns a field element to each variable index,
- `data` stores additional prover-side data that is not part of the current witness.

## Evaluation

Expressions are evaluated in an environment by:

```lean
def eval (env : Environment F) : Expression F → F
  | var v => env.get v.index
  | const c => c
  | add x y => eval env x + eval env y
  | mul x y => eval env x * eval env y
```

There is also a coercion

```lean
instance [Field F] : CoeFun (Environment F) (fun _ => (Expression F) → F)
```

so an environment can be used as a function. That is why Clean code often writes:

```lean
env x
```

instead of:

```lean
Expression.eval env x
```
