/-
Extracted from LinearAlgebra/Matrix/Notation.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

public meta import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Matrix and vector notation

This file includes `simp` lemmas for applying operations in `Data.Matrix.Basic` to values built out
of the matrix notation `![a, b] = vecCons a (vecCons b vecEmpty)` defined in
`Data.Fin.VecNotation`.

This also provides the new notation `!![a, b; c, d] = Matrix.of ![![a, b], ![c, d]]`.
This notation also works for empty matrices; `!![,,,] : Matrix (Fin 0) (Fin 3)` and
`!![;;;] : Matrix (Fin 3) (Fin 0)`.

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vecCons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notation

This file provide notation `!![a, b; c, d]` for matrices, which corresponds to
`Matrix.of ![![a, b], ![c, d]]`.

## Examples

Examples of usage can be found in the `MathlibTest/matrix.lean` file.
-/

namespace Matrix

universe u uₘ uₙ uₒ

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

open Matrix

section toExpr

open Lean Qq

open Qq in

meta def mkLiteralQ {u : Level} {α : Q(Type u)} {m n : Nat} (elems : Matrix (Fin m) (Fin n) Q($α)) :
    Q(Matrix (Fin $m) (Fin $n) $α) :=
  let elems := PiFin.mkLiteralQ (α := q(Fin $n → $α)) fun i => PiFin.mkLiteralQ fun j => elems i j
  q(Matrix.of $elems)

-- INSTANCE (free from Core): toExpr

end toExpr

section Parser

open Lean Meta Elab Term Macro TSyntax PrettyPrinter.Delaborator SubExpr

syntax (name := matrixNotation)

  "!![" ppRealGroup(sepBy1(ppGroup(term,+,?), ";", "; ", allowTrailingSep)) "]" : term
