/-
Extracted from Algebra/Lie/Killing.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lie algebras with non-degenerate Killing forms.

In characteristic zero, the following three conditions are equivalent:
 1. The solvable radical of a Lie algebra is trivial
 2. A Lie algebra is a direct sum of its simple ideals
 3. A Lie algebra has non-degenerate Killing form

In positive characteristic, it is still true that 3 implies 2, and that 2 implies 1, but there are
counterexamples to the remaining implications. Thus condition 3 is the strongest assumption.
Furthermore, much of the Cartan-Killing classification of semisimple Lie algebras in characteristic
zero, continues to hold in positive characteristic (over a perfect field) if the Lie algebra has a
non-degenerate Killing form.

This file contains basic definitions and results for such Lie algebras.

## Main declarations

* `LieAlgebra.IsKilling`: a typeclass encoding the fact that a Lie algebra has a non-singular
  Killing form.
* `LieAlgebra.IsKilling.instSemisimple`: if a finite-dimensional Lie algebra over a field
  has non-singular Killing form then it is semisimple.
* `LieAlgebra.IsKilling.instHasTrivialRadical`: if a Lie algebra over a PID
  has non-singular Killing form then it has trivial radical.
* `LieIdeal.isCompl_killingCompl`: if a Lie algebra has non-singular Killing form then for all
  ideals, an ideal and its Killing orthogonal complement are complements.

## TODO

* Prove that in characteristic zero, a semisimple Lie algebra has non-singular Killing form.

-/

variable (R K L : Type*) [CommRing R] [Field K] [LieRing L] [LieAlgebra R L] [LieAlgebra K L]

namespace LieAlgebra

class IsKilling : Prop where
  /-- We say a Lie algebra is Killing if its Killing form is non-singular. -/
  killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥

attribute [simp] IsKilling.killingCompl_top_eq_bot

namespace IsKilling

variable [IsKilling R L]
