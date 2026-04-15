/-
Extracted from CategoryTheory/Functor/Derived/RightDerived.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Right derived functors

In this file, given a functor `F : C ⥤ H`, and `L : C ⥤ D` that is a
localization functor for `W : MorphismProperty C`, we define
`F.totalRightDerived L W : D ⥤ H` as the left Kan extension of `F`
along `L`: it is defined if the type class `F.HasRightDerivedFunctor W`
asserting the existence of a left Kan extension is satisfied.
(The name `totalRightDerived` is to avoid name-collision with
`Functor.rightDerived` which are the right derived functors in
the context of abelian categories.)

Given `RF : D ⥤ H` and `α : F ⟶ L ⋙ RF`, we also introduce a type class
`F.IsRightDerivedFunctor α W` saying that `α` is a left Kan extension of `F`
along the localization functor `L`.

## TODO

- refactor `Functor.rightDerived` (and `Functor.leftDerived`) when the necessary
  material enters mathlib: derived categories, injective/projective derivability
  structures, existence of derived functors from derivability structures.

## References

* https://ncatlab.org/nlab/show/derived+functor

-/

namespace CategoryTheory

namespace Functor

variable {C C' D D' H H' : Type _} [Category* C] [Category* C']
  [Category* D] [Category* D'] [Category* H] [Category* H']
  (RF RF' RF'' : D ⥤ H) {F F' F'' : C ⥤ H} (e : F ≅ F') {L : C ⥤ D}
  (α : F ⟶ L ⋙ RF) (α' : F' ⟶ L ⋙ RF') (α'' : F'' ⟶ L ⋙ RF'') (α'₂ : F ⟶ L ⋙ RF')
  (W : MorphismProperty C)

class IsRightDerivedFunctor (RF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : F ⟶ L ⋙ RF)
    (W : MorphismProperty C) [L.IsLocalization W] : Prop where
  isLeftKanExtension (RF α) : RF.IsLeftKanExtension α

lemma isRightDerivedFunctor_iff_isLeftKanExtension [L.IsLocalization W] :
    RF.IsRightDerivedFunctor α W ↔ RF.IsLeftKanExtension α := by
  constructor
  · exact fun _ => IsRightDerivedFunctor.isLeftKanExtension RF α W
  · exact fun h => ⟨h⟩

variable {RF RF'} in

lemma isRightDerivedFunctor_iff_of_iso (α' : F ⟶ L ⋙ RF') (W : MorphismProperty C)
    [L.IsLocalization W] (e : RF ≅ RF') (comm : α ≫ whiskerLeft L e.hom = α') :
    RF.IsRightDerivedFunctor α W ↔ RF'.IsRightDerivedFunctor α' W := by
  simp only [isRightDerivedFunctor_iff_isLeftKanExtension]
  exact isLeftKanExtension_iff_of_iso e _ _ comm

variable [L.IsLocalization W] [RF.IsRightDerivedFunctor α W]

noncomputable def rightDerivedDesc (G : D ⥤ H) (β : F ⟶ L ⋙ G) : RF ⟶ G :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension α G β
