/-
Extracted from CategoryTheory/Core.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The core of a category

The core of a category `C` is the (non-full) subcategory of `C` consisting of all objects,
and all isomorphisms. We construct it as a `CategoryTheory.Groupoid`.

`CategoryTheory.Core.inclusion : Core C ⥤ C` gives the faithful inclusion into the original
category.

Any functor `F` from a groupoid `G` into `C` factors through `CategoryTheory.Core C`,
but this is not functorial with respect to `F`.
-/

namespace CategoryTheory

open Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

structure Core (C : Type u₁) where
  /-- The object of the base category underlying an object in `Core C`. -/
  of : C

variable {C : Type u₁} [Category.{v₁} C]
