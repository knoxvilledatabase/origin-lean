/-
Extracted from CategoryTheory/GuitartExact/KanExtension.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Guitart exact squares and Kan extensions

Given a Guitart exact square `w : T ⋙ R ⟶ L ⋙ B`,
```
     T
  C₁ ⥤ C₂
L |     | R
  v     v
  C₃ ⥤ C₄
     B
```
we show that an extension `F' : C₄ ⥤ D` of `F : C₂ ⥤ D` along `R`
is a pointwise left Kan extension at `B.obj X₃` iff
the composition `T ⋙ F'` is a pointwise left Kan extension at `X₃`
of `B ⋙ F'`.

When suitable (pointwise) left Kan extensions exist, we also show that
the natural transformation of functors `(C₂ ⥤ D) ⥤ C₃ ⥤ D`
`(whiskeringLeft C₁ C₂ D).obj T ⋙ L.lan ⟶ R.lan ⋙ (whiskeringLeft C₃ C₄ D).obj B`
induced by a Guitart exact square `w` is an isomorphism.

## References

* https://ncatlab.org/nlab/show/exact+square

-/

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} {D : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Category.{v₅} D]

namespace Functor.LeftExtension

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  {F : C₂ ⥤ D} (E : R.LeftExtension F)

abbrev compTwoSquare (w : TwoSquare T L R B) : L.LeftExtension (T ⋙ F) :=
  LeftExtension.mk (B ⋙ E.right)
    (whiskerLeft _ E.hom ≫ (associator _ _ _).inv ≫
      whiskerRight w.natTrans _ ≫ (associator _ _ _).hom)

noncomputable def isPointwiseLeftKanExtensionAtCompTwoSquareEquiv
    (w : TwoSquare T L R B) (X₃ : C₃) [Final (w.costructuredArrowRightwards X₃)] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtensionAt X₃ ≃
      E.IsPointwiseLeftKanExtensionAt (B.obj X₃) := by
  refine Equiv.trans ?_ (Final.isColimitWhiskerEquiv (w.costructuredArrowRightwards X₃) _)
  exact IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _))

lemma nonempty_isPointwiseLeftKanExtensionAt_compTwoSquare_iff
    (w : TwoSquare T L R B) (X₃ : C₃) [Final (w.costructuredArrowRightwards X₃)] :
    Nonempty ((E.compTwoSquare w).IsPointwiseLeftKanExtensionAt X₃) ↔
      Nonempty (E.IsPointwiseLeftKanExtensionAt (B.obj X₃)) :=
  (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _).nonempty_congr

variable {E} in

noncomputable def IsPointwiseLeftKanExtension.compTwoSquare
    (h : E.IsPointwiseLeftKanExtension) (w : TwoSquare T L R B) [w.GuitartExact] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtension :=
  fun X₃ ↦ (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w X₃).symm (h _)

noncomputable def isPointwiseLeftKanExtensionOfCompTwoSquare
    (w : TwoSquare T L R B) [w.GuitartExact] [B.EssSurj]
    (h : (E.compTwoSquare w).IsPointwiseLeftKanExtension) :
    E.IsPointwiseLeftKanExtension :=
  fun X₄ ↦ E.isPointwiseLeftKanExtensionAtOfIso'
    (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _ (h (B.objPreimage X₄)))
    (B.objObjPreimageIso X₄)

noncomputable def isPointwiseLeftKanExtensionEquivOfGuitartExact
    (w : TwoSquare T L R B) [w.GuitartExact] [B.EssSurj] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtension ≃
      E.IsPointwiseLeftKanExtension where
  toFun h := E.isPointwiseLeftKanExtensionOfCompTwoSquare w h
  invFun h := h.compTwoSquare w
  left_inv _ := by subsingleton
  right_inv _ := by subsingleton

end Functor.LeftExtension

namespace TwoSquare

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
   (w : TwoSquare T L R B)

include w

lemma hasPointwiseLeftKanExtensionAt_iff
    (F : C₂ ⥤ D) (X₃ : C₃) [(w.costructuredArrowRightwards X₃).Final] :
    L.HasPointwiseLeftKanExtensionAt (T ⋙ F) X₃ ↔
      R.HasPointwiseLeftKanExtensionAt F (B.obj X₃) := by
  dsimp [Functor.HasPointwiseLeftKanExtensionAt]
  rw [← Functor.Final.hasColimit_comp_iff (w.costructuredArrowRightwards X₃)]
  rfl

lemma hasPointwiseLeftKanExtension_iff [w.GuitartExact] [B.EssSurj] (F : C₂ ⥤ D) :
    L.HasPointwiseLeftKanExtension (T ⋙ F) ↔
      R.HasPointwiseLeftKanExtension F := by
  dsimp [Functor.HasPointwiseLeftKanExtension]
  simp only [hasPointwiseLeftKanExtensionAt_iff w]
  refine ⟨fun h X₄ ↦ ?_, fun h _ ↦ h _⟩
  rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso _ _ (B.objObjPreimageIso X₄)]
  apply h

lemma hasPointwiseLeftKanExtension [w.GuitartExact]
    (F : C₂ ⥤ D) [R.HasPointwiseLeftKanExtension F] :
    L.HasPointwiseLeftKanExtension (T ⋙ F) :=
  ((R.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    F).compTwoSquare w).hasPointwiseLeftKanExtension

lemma hasLeftKanExtension [w.GuitartExact]
    (F : C₂ ⥤ D) [R.HasPointwiseLeftKanExtension F] :
    L.HasLeftKanExtension (T ⋙ F) := by
  have := w.hasPointwiseLeftKanExtension F
  infer_instance

open Functor

variable [∀ (F : C₁ ⥤ D), L.HasLeftKanExtension F] [∀ (F : C₂ ⥤ D), R.HasLeftKanExtension F]

set_option backward.isDefEq.respectTransparency false in
