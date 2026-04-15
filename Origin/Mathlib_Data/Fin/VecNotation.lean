/-
Extracted from Data/Fin/VecNotation.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matrix and vector notation

This file defines notation for vectors and matrices. Given `a b c d : α`,
the notation allows us to write `![a, b, c, d] : Fin 4 → α`.
Nesting vectors gives coefficients of a matrix, so `![![a, b], ![c, d]] : Fin 2 → Fin 2 → α`.
In later files we introduce `!![a, b; c, d]` as notation for `Matrix.of ![![a, b], ![c, d]]`.

## Main definitions

* `vecEmpty` is the empty vector (or `0` by `n` matrix) `![]`
* `vecCons` prepends an entry to a vector, so `![a, b]` is `vecCons a (vecCons b vecEmpty)`

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vecCons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notation

The main new notation is `![a, b]`, which gets expanded to `vecCons a (vecCons b vecEmpty)`.

## Examples

Examples of usage can be found in the `MathlibTest/matrix.lean` file.
-/

namespace Matrix

universe u

variable {α : Type u}

section MatrixNotation

def vecEmpty : Fin 0 → α :=
  Fin.elim0

def vecCons {n : ℕ} (h : α) (t : Fin n → α) : Fin n.succ → α :=
  Fin.cons h t

syntax (name := vecNotation) "![" term,* "]" : term

macro_rules

  | `(![$term:term, $terms:term,*]) => `(vecCons $term ![$terms,*])

  | `(![$term:term]) => `(vecCons $term ![])

  | `(![]) => `(vecEmpty)
