/-
Extracted from CategoryTheory/GradedObject/Single.lean
Genuine: 10 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.GradedObject

noncomputable section

/-!
# The graded object in a single degree

In this file, we define the functor `GradedObject.single j : C ⥤ GradedObject J C`
which sends an object `X : C` to the graded object which is `X` in degree `j` and
the initial object of `C` in other degrees.

-/

namespace CategoryTheory

open Limits

namespace GradedObject

variable {J : Type*} {C : Type*} [Category C] [HasInitial C] [DecidableEq J]

noncomputable def single (j : J) : C ⥤ GradedObject J C where
  obj X i := if i = j then X else ⊥_ C
  map {X₁ X₂} f i :=
    if h : i = j then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else eqToHom (by dsimp; rw [if_neg h, if_neg h])

variable (J) in

noncomputable abbrev single₀ [Zero J] : C ⥤ GradedObject J C := single 0

noncomputable def singleObjApplyIsoOfEq (j : J) (X : C) (i : J) (h : i = j) :
    (single j).obj X i ≅ X := eqToIso (if_pos h)

noncomputable abbrev singleObjApplyIso (j : J) (X : C) :
    (single j).obj X j ≅ X := singleObjApplyIsoOfEq j X j rfl

noncomputable def isInitialSingleObjApply (j : J) (X : C) (i : J) (h : i ≠ j) :
    IsInitial ((single j).obj X i) := by
  dsimp [single]
  rw [if_neg h]
  exact initialIsInitial

lemma singleObjApplyIsoOfEq_inv_single_map (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j) :
    (singleObjApplyIsoOfEq j X i h).inv ≫ (single j).map f i =
      f ≫ (singleObjApplyIsoOfEq j Y i h).inv := by
  subst h
  simp [singleObjApplyIsoOfEq, single]

lemma single_map_singleObjApplyIsoOfEq_hom (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j) :
    (single j).map f i ≫ (singleObjApplyIsoOfEq j Y i h).hom =
      (singleObjApplyIsoOfEq j X i h).hom ≫ f := by
  subst h
  simp [singleObjApplyIsoOfEq, single]

@[reassoc (attr := simp)]
lemma singleObjApplyIso_inv_single_map (j : J) {X Y : C} (f : X ⟶ Y) :
    (singleObjApplyIso j X).inv ≫ (single j).map f j = f ≫ (singleObjApplyIso j Y).inv := by
  apply singleObjApplyIsoOfEq_inv_single_map

@[reassoc (attr := simp)]
lemma single_map_singleObjApplyIso_hom (j : J) {X Y : C} (f : X ⟶ Y) :
    (single j).map f j ≫ (singleObjApplyIso j Y).hom = (singleObjApplyIso j X).hom ≫ f := by
  apply single_map_singleObjApplyIsoOfEq_hom

variable (C) in

@[simps!]
noncomputable def singleCompEval (j : J) : single j ⋙ eval j ≅ 𝟭 C :=
  NatIso.ofComponents (singleObjApplyIso j) (by aesop_cat)

end GradedObject

end CategoryTheory
