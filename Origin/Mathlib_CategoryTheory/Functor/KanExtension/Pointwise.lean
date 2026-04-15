/-
Extracted from CategoryTheory/Functor/KanExtension/Pointwise.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pointwise Kan extensions

In this file, we define the notion of pointwise (left) Kan extension. Given two functors
`L : C ⥤ D` and `F : C ⥤ H`, and `E : LeftExtension L F`, we introduce a cocone
`E.coconeAt Y` for the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H`
the point of which is `E.right.obj Y`, and the type `E.IsPointwiseLeftKanExtensionAt Y`
which expresses that `E.coconeAt Y` is a colimit. When this holds for all `Y : D`,
we may say that `E` is a pointwise left Kan extension (`E.IsPointwiseLeftKanExtension`).

Conversely, when `CostructuredArrow.proj L Y ⋙ F` has a colimit, we say that
`F` has a pointwise left Kan extension at `Y : D` (`HasPointwiseLeftKanExtensionAt L F Y`),
and if this holds for all `Y : D`, we construct a functor
`pointwiseLeftKanExtension L F : D ⥤ H` and show it is a pointwise Kan extension.

A dual API for pointwise right Kan extension is also formalized.

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D D' H : Type*} [Category* C] [Category* D] [Category* D'] [Category* H]
  (L : C ⥤ D) (L' : C ⥤ D') (F : C ⥤ H)

abbrev HasPointwiseLeftKanExtensionAt (Y : D) :=
  HasColimit (CostructuredArrow.proj L Y ⋙ F)

abbrev HasPointwiseLeftKanExtension := ∀ (Y : D), HasPointwiseLeftKanExtensionAt L F Y

abbrev HasPointwiseRightKanExtensionAt (Y : D) :=
  HasLimit (StructuredArrow.proj Y L ⋙ F)

abbrev HasPointwiseRightKanExtension := ∀ (Y : D), HasPointwiseRightKanExtensionAt L F Y

lemma hasPointwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) :
    HasPointwiseLeftKanExtensionAt L F Y₁ ↔
      HasPointwiseLeftKanExtensionAt L F Y₂ := by
  revert Y₁ Y₂ e
  suffices ∀ ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseLeftKanExtensionAt L F Y₁],
      HasPointwiseLeftKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasColimit ((CostructuredArrow.mapIso e.symm).functor ⋙ CostructuredArrow.proj L Y₁ ⋙ F)
  infer_instance

lemma hasPointwiseRightKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) :
    HasPointwiseRightKanExtensionAt L F Y₁ ↔
      HasPointwiseRightKanExtensionAt L F Y₂ := by
  revert Y₁ Y₂ e
  suffices ∀ ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseRightKanExtensionAt L F Y₁],
      HasPointwiseRightKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasLimit ((StructuredArrow.mapIso e.symm).functor ⋙ StructuredArrow.proj Y₁ L ⋙ F)
  infer_instance

variable {L} in

lemma hasPointwiseLeftKanExtensionAt_iff_of_natIso {L' : C ⥤ D} (e : L ≅ L') (Y : D) :
    HasPointwiseLeftKanExtensionAt L F Y ↔
      HasPointwiseLeftKanExtensionAt L' F Y := by
  revert L L' e
  suffices ∀ ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseLeftKanExtensionAt L F Y],
      HasPointwiseLeftKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : CostructuredArrow L' Y ≌ CostructuredArrow L Y := Comma.mapLeftIso _ e.symm
  let e' : CostructuredArrow.proj L' Y ⋙ F ≅
    Φ.functor ⋙ CostructuredArrow.proj L Y ⋙ F := Iso.refl _
  exact hasColimit_of_iso e'

variable {L} in

lemma hasPointwiseRightKanExtensionAt_iff_of_natIso {L' : C ⥤ D} (e : L ≅ L') (Y : D) :
    HasPointwiseRightKanExtensionAt L F Y ↔
      HasPointwiseRightKanExtensionAt L' F Y := by
  revert L L' e
  suffices ∀ ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseRightKanExtensionAt L F Y],
      HasPointwiseRightKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : StructuredArrow Y L' ≌ StructuredArrow Y L := Comma.mapRightIso _ e.symm
  let e' : StructuredArrow.proj Y L' ⋙ F ≅
    Φ.functor ⋙ StructuredArrow.proj Y L ⋙ F := Iso.refl _
  exact hasLimit_of_iso e'.symm

lemma hasPointwiseLeftKanExtensionAt_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y')
    [HasPointwiseLeftKanExtensionAt L F Y] :
    HasPointwiseLeftKanExtensionAt L' F Y' := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_natIso F eL,
    hasPointwiseLeftKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := CostructuredArrow.post L E.functor Y
  have : HasColimit ((asEquivalence Φ).functor ⋙
    CostructuredArrow.proj (L ⋙ E.functor) (E.functor.obj Y) ⋙ F) :=
    (inferInstance : HasPointwiseLeftKanExtensionAt L F Y)
  exact hasColimit_of_equivalence_comp (asEquivalence Φ)

lemma hasPointwiseLeftKanExtensionAt_iff_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') :
    HasPointwiseLeftKanExtensionAt L F Y ↔
      HasPointwiseLeftKanExtensionAt L' F Y' := by
  constructor
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnitor) Y' Y
      (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app Y)

lemma hasPointwiseRightKanExtensionAt_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y')
    [HasPointwiseRightKanExtensionAt L F Y] :
    HasPointwiseRightKanExtensionAt L' F Y' := by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_natIso F eL,
    hasPointwiseRightKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := StructuredArrow.post Y L E.functor
  have : HasLimit ((asEquivalence Φ).functor ⋙
    StructuredArrow.proj (E.functor.obj Y) (L ⋙ E.functor) ⋙ F) :=
    (inferInstance : HasPointwiseRightKanExtensionAt L F Y)
  exact hasLimit_of_equivalence_comp (asEquivalence Φ)

lemma hasPointwiseRightKanExtensionAt_iff_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') :
    HasPointwiseRightKanExtensionAt L F Y ↔
      HasPointwiseRightKanExtensionAt L' F Y' := by
  constructor
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnitor) Y' Y
      (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app Y)

namespace LeftExtension

variable {F L}

variable (E : LeftExtension L F)

set_option backward.isDefEq.respectTransparency false in
