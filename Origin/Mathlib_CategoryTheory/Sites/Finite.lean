/-
Extracted from CategoryTheory/Sites/Finite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # The Finite Pretopology

In this file we define the finite pretopology on a category, which consists of presieves that
contain only finitely many arrows.

## Main Definitions

- `CategoryTheory.Precoverage.finite`: The finite precoverage on a category.
- `CategoryTheory.Pretopology.finite`: The finite pretopology on a category.
-/

universe v v₁ u u₁

namespace CategoryTheory

open Presieve

namespace Precoverage

def finite (C : Type u) [Category.{v} C] : Precoverage C where
  coverings X := { s : Presieve X | s.uncurry.Finite }

variable {C : Type u} [Category.{v} C]
