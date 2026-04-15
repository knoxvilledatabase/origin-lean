/-
Extracted from CategoryTheory/Filtered/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Filtered categories

A category is filtered if every finite diagram admits a cocone.
We give a simple characterisation of this condition as
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

An important example of filtered category is given by nonempty directed types;
actually, filtered categories may be considered as a generalization of nonempty directed types.
In the file `CategoryTheory.Presentable.Directed`, we show that "conversely"
if `C` is a filtered category, there exists a final functor `α ⥤ C` from
a nonempty directed type (`IsFiltered.isDirected`).

Filtered colimits are often better behaved than arbitrary colimits.
See `Mathlib/CategoryTheory/Limits/Types/` for some details.

Filtered categories are nice because colimits indexed by filtered categories tend to be
easier to describe than general colimits (and more often preserved by functors).

In this file we show that any functor from a finite category to a filtered category admits a cocone:
* `cocone_nonempty [FinCategory J] [IsFiltered C] (F : J ⥤ C) : Nonempty (Cocone F)`
More generally,
for any finite collection of objects and morphisms between them in a filtered category
(even if not closed under composition) there exists some object `Z` receiving maps from all of them,
so that all the triangles (one edge from the finite set, two from morphisms to `Z`) commute.
This formulation is often more useful in practice and is available via `sup_exists`,
which takes a finset of objects, and an indexed family (indexed by source and target)
of finsets of morphisms.

We also prove the converse of `cocone_nonempty` as `of_cocone_nonempty`.

Furthermore, we give special support for two diagram categories: The `bowtie` and the `tulip`.
This is because these shapes show up in the proofs that forgetful functors of algebraic categories
(e.g. `MonCat`, `CommRingCat`, ...) preserve filtered colimits.

All of the above API, except for the `bowtie` and the `tulip`, is also provided for cofiltered
categories.

## See also
In `Mathlib/CategoryTheory/Limits/FilteredColimitCommutesFiniteLimit.lean` we show that filtered
colimits commute with finite limits.

There is another characterization of filtered categories, namely that whenever `F : J ⥤ C` is a
functor from a finite category, there is `X : C` such that `Nonempty (limit (F.op ⋙ yoneda.obj X))`.
This is shown in `Mathlib/CategoryTheory/Limits/Filtered.lean`.

-/

open Function

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory

attribute [local instance] uliftCategory

variable (C : Type u) [Category.{v} C]

class IsFilteredOrEmpty : Prop where
  /-- for every pair of objects there exists another object "to the right" -/
  cocone_objs : ∀ X Y : C, ∃ (Z : _) (_ : X ⟶ Z) (_ : Y ⟶ Z), True
  /-- for every pair of parallel morphisms there exists a morphism to the right
  so the compositions are equal -/
  cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ (Z : _) (h : Y ⟶ Z), f ≫ h = g ≫ h
