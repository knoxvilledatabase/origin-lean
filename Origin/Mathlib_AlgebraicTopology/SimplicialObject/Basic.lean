/-
Extracted from AlgebraicTopology/SimplicialObject/Basic.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Simplicial objects in a category.

A simplicial object in a category `C` is a `C`-valued presheaf on `SimplexCategory`.
(Similarly, a cosimplicial object is a functor `SimplexCategory ⥤ C`.)

## Notation

The following notations can be enabled via `open Simplicial`.

- `X _⦋n⦌` denotes the `n`-th term of a simplicial object `X`, where `n : ℕ`.
- `X ^⦋n⦌` denotes the `n`-th term of a cosimplicial object `X`, where `n : ℕ`.

The following notations can be enabled via
`open CategoryTheory.SimplicialObject.Truncated`.

- `X _⦋m⦌ₙ` denotes the `m`-th term of an `n`-truncated simplicial object `X`.
- `X ^⦋m⦌ₙ` denotes the `m`-th term of an `n`-truncated cosimplicial object `X`.
-/

open Opposite

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

abbrev SimplicialObject :=
  SimplexCategoryᵒᵖ ⥤ C

namespace SimplicialObject

set_option quotPrecheck false in

scoped[Simplicial]

  notation3:1000 X " _⦋" n "⦌" =>

      (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

open Simplicial

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): [HasLimits

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): [HasColimits

variable {C}
