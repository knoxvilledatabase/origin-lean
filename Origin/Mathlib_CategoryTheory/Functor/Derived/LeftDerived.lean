/-
Extracted from CategoryTheory/Functor/Derived/LeftDerived.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Left derived functors

In this file, given a functor `F : C ⥤ H`, and `L : C ⥤ D` that is a
localization functor for `W : MorphismProperty C`, we define
`F.totalLeftDerived L W : D ⥤ H` as the right Kan extension of `F`
along `L`: it is defined if the type class `F.HasLeftDerivedFunctor W`
asserting the existence of a right Kan extension is satisfied.
(The name `totalLeftDerived` is to avoid name-collision with
`Functor.leftDerived` which are the left derived functors in
the context of abelian categories.)

Given `LF : D ⥤ H` and `α : L ⋙ LF ⟶ F`, we also introduce a type class
`F.IsLeftDerivedFunctor α W` saying that `α` is a right Kan extension of `F`
along the localization functor `L`.

(This file was obtained by dualizing the results in the file
`Mathlib.CategoryTheory.Functor.Derived.RightDerived`.)

## References

* https://ncatlab.org/nlab/show/derived+functor

-/

namespace CategoryTheory

namespace Functor

variable {C C' D D' H H' : Type _} [Category* C] [Category* C']
  [Category* D] [Category* D'] [Category* H] [Category* H']
  (LF'' LF' LF : D ⥤ H) {F F' F'' : C ⥤ H} (e : F ≅ F') {L : C ⥤ D}
  (α'' : L ⋙ LF'' ⟶ F'') (α' : L ⋙ LF' ⟶ F') (α : L ⋙ LF ⟶ F) (α'₂ : L ⋙ LF' ⟶ F)
  (W : MorphismProperty C)

class IsLeftDerivedFunctor (LF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : L ⋙ LF ⟶ F)
    (W : MorphismProperty C) [L.IsLocalization W] : Prop where
  isRightKanExtension (LF α) : LF.IsRightKanExtension α

lemma isLeftDerivedFunctor_iff_isRightKanExtension [L.IsLocalization W] :
    LF.IsLeftDerivedFunctor α W ↔ LF.IsRightKanExtension α := by
  constructor
  · exact fun _ => IsLeftDerivedFunctor.isRightKanExtension LF α W
  · exact fun h => ⟨h⟩

variable {RF RF'} in

lemma isLeftDerivedFunctor_iff_of_iso (α' : L ⋙ LF' ⟶ F) (W : MorphismProperty C)
    [L.IsLocalization W] (e : LF ≅ LF') (comm : whiskerLeft L e.hom ≫ α' = α) :
    LF.IsLeftDerivedFunctor α W ↔ LF'.IsLeftDerivedFunctor α' W := by
  simp only [isLeftDerivedFunctor_iff_isRightKanExtension]
  exact isRightKanExtension_iff_of_iso e _ _ comm

variable [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]

noncomputable def leftDerivedLift (G : D ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ LF :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension α G β
