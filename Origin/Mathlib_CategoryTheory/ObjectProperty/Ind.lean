/-
Extracted from CategoryTheory/ObjectProperty/Ind.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Ind and pro-properties

Given an object property `P`, we define an object property `ind P` that is satisfied for
`X` if `X` is a filtered colimit of `Xᵢ` and `Xᵢ` satisfies `P`.

## Main definitions

- `CategoryTheory.ObjectProperty.ind`: `X` satisfies `ind P` if `X` is a filtered colimit of `Xᵢ`
  for `Xᵢ` in `P`.

## Main results

- `CategoryTheory.ObjectProperty.ind_ind`: If `P` implies finitely presentable, then
  `P.ind.ind = P.ind`.

## TODOs:

- Dualise to obtain `CategoryTheory.ObjectProperty.pro`.
-/

universe w v u

namespace CategoryTheory.ObjectProperty

open Limits Opposite

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

def ind (P : ObjectProperty C) : ObjectProperty C :=
  fun X ↦ ∃ (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (pres : ColimitPresentation J X), ∀ i, P (pres.diag.obj i)

variable (P) in

lemma le_ind : P ≤ ind.{w} P := by
  intro X hX
  exact ⟨PUnit, inferInstance, inferInstance, .self X, by simpa⟩

-- INSTANCE (free from Core): [P.Nonempty]

-- INSTANCE (free from Core): :

lemma of_essentiallySmall_index {X : C} {J : Type*} [Category* J] [EssentiallySmall.{w} J]
    [IsFiltered J] (pres : ColimitPresentation J X) (h : ∀ i, P (pres.diag.obj i)) :
    ind.{w} P X :=
  ⟨SmallModel J, inferInstance, .of_equivalence (equivSmallModel _),
    pres.reindex (equivSmallModel _).inverse, fun _ ↦ h _⟩

lemma ind_iff_exists (H : P ≤ isFinitelyPresentable.{w} C)
    [IsFinitelyAccessibleCategory.{w} C] {X : C} :
    ind.{w} P X ↔ ∀ {Z : C} (g : Z ⟶ X) [IsFinitelyPresentable.{w} Z],
      ∃ (W : C) (u : Z ⟶ W) (v : W ⟶ X), u ≫ v = g ∧ P W := by
  refine ⟨fun ⟨J, _, _, pres, h⟩ Z g hZ ↦ ?_, fun hfac ↦ ?_⟩
  · have : IsFinitelyPresentable Z := hZ
    obtain ⟨j, u, hcomp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit g
    exact ⟨_, u, pres.ι.app j, hcomp, h j⟩
  · let incl : P.FullSubcategory ⥤ (isFinitelyPresentable.{w} C).FullSubcategory :=
      ObjectProperty.ιOfLE H
    have H (d : CostructuredArrow (isFinitelyPresentable.{w} C).ι X) : ∃ c,
        Nonempty (d ⟶ (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X).obj c) := by
      obtain ⟨W, u, v, huv, hW⟩ := hfac d.hom
      exact ⟨CostructuredArrow.mk (Y := FullSubcategory.mk _ hW) v,
        ⟨CostructuredArrow.homMk ⟨u⟩ huv⟩⟩
    have : (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X).Final :=
      Functor.final_of_exists_of_isFiltered_of_fullyFaithful (C := CostructuredArrow (incl ⋙ _) X)
        (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X) H
    have : IsFiltered (CostructuredArrow P.ι X) :=
      .of_exists_of_isFiltered_of_fullyFaithful (C := CostructuredArrow (incl ⋙ _) X)
        (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X) H
    obtain ⟨hc⟩ : P.ι.isDenseAt X :=
      Functor.IsDenseAt.of_final (F := (isFinitelyPresentable.{w} C).ι) incl
        (Functor.IsDense.isDenseAt _ _)
    have : EssentiallySmall.{w} (CostructuredArrow P.ι X) :=
      essentiallySmall_of_fully_faithful (C := CostructuredArrow (incl ⋙ _) X)
        (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X)
    exact of_essentiallySmall_index ⟨_, _, hc⟩ fun Y ↦ Y.left.2

end CategoryTheory.ObjectProperty
