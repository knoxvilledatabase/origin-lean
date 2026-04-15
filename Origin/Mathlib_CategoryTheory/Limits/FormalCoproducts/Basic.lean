/-
Extracted from CategoryTheory/Limits/FormalCoproducts/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Formal Coproducts

In this file we construct the category of formal coproducts given a category.

## Main definitions

* `FormalCoproduct`: the category of formal coproducts, which are indexed sets of objects in a
  category. A morphism `∐ i : X.I, X.obj i ⟶ ∐ j : Y.I, Y.obj j` is given by a function
  `f : X.I → Y.I` and maps `X.obj i ⟶ Y.obj (f i)` for each `i : X.I`.
* `FormalCoproduct.eval : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct C)ᵒᵖ ⥤ A)`:
  the universal property that a presheaf on `C` where the target category has arbitrary coproducts,
  can be extended to a presheaf on `FormalCoproduct C`.

## TODO

* `FormalCoproduct.incl C : C ⥤ FormalCoproduct.{w} C` probably preserves every limit?

-/

universe w w₁ w₂ w₃ v v₁ v₂ v₃ u u₁ u₂ u₃

open Opposite CategoryTheory Functor

namespace CategoryTheory

namespace Limits

variable {C : Type u} [Category.{v} C] (A : Type u₁) [Category.{v₁} A]

variable (C) in

structure FormalCoproduct where
  /-- The indexing type. -/
  I : Type w
  /-- The object in the original category indexed by `x : I`. -/
  obj (i : I) : C

namespace FormalCoproduct

structure Hom (X Y : FormalCoproduct.{w} C) where
  /-- The function on the indexing sets. -/
  f : X.I → Y.I
  /-- The map on each component. -/
  φ (i : X.I) : X.obj i ⟶ Y.obj (f i)
