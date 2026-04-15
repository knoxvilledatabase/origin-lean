/-
Extracted from CategoryTheory/Enriched/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Enriched categories

We set up the basic theory of `V`-enriched categories,
for `V` an arbitrary monoidal category.

We do not assume here that `V` is a concrete category,
so there does not need to be an "honest" underlying category!

Use `X ⟶[V] Y` to obtain the `V` object of morphisms from `X` to `Y`.

This file contains the definitions of `V`-enriched categories and
`V`-functors.

We don't yet define the `V`-object of natural transformations
between a pair of `V`-functors (this requires limits in `V`),
but we do provide a presheaf isomorphic to the Yoneda embedding of this object.

We verify that when `V = Type v`, all these notions reduce to the usual ones.

## References

* [Kim Morrison, David Penneys, _Monoidal Categories Enriched in Braided Monoidal Categories_]
  [morrison-penney-enriched]
-/

universe w w' v v' u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Opposite

open MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

class EnrichedCategory (C : Type u₁) where
  /-- `X ⟶[V] Y` is the `V` object of morphisms from `X` to `Y`. -/
  Hom : C → C → V
  /-- The identity morphism of this category -/
  id (X : C) : 𝟙_ V ⟶ Hom X X
  /-- Composition of two morphisms in this category -/
  comp (X Y Z : C) : Hom X Y ⊗ Hom Y Z ⟶ Hom X Z
  id_comp (X Y : C) : (λ_ (Hom X Y)).inv ≫ id X ▷ _ ≫ comp X X Y = 𝟙 _ := by cat_disch
  comp_id (X Y : C) : (ρ_ (Hom X Y)).inv ≫ _ ◁ id Y ≫ comp X Y Y = 𝟙 _ := by cat_disch
  assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ comp W X Y ▷ _ ≫ comp W Y Z =
    _ ◁ comp X Y Z ≫ comp W X Z := by cat_disch
