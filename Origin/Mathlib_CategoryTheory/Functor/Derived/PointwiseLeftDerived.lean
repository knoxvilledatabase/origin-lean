/-
Extracted from CategoryTheory/Functor/Derived/PointwiseLeftDerived.lean
Genuine: 15 of 16 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Pointwise left derived functors

We define pointwise left derived functors using the notion
of pointwise right Kan extensions.

We show that if `F : C ⥤ H` inverts `W : MorphismProperty C`,
then it has a pointwise left derived functor.

Note: this file was obtained by dualizing the definitions in the file
`Mathlib/CategoryTheory/Functor/Derived/PointwiseRightDerived.lean`. These two files should be
kept in sync.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
  (F' : D ⥤ H) (F : C ⥤ H) (L : C ⥤ D) (α : L ⋙ F' ⟶ F) (W : MorphismProperty C)

class HasPointwiseLeftDerivedFunctorAt (X : C) : Prop where
  /-- Use the more general `hasLimit` lemma instead, see also
  `hasPointwiseLeftDerivedFunctorAt_iff` -/
  hasLimit' : HasPointwiseRightKanExtensionAt W.Q F (W.Q.obj X)

abbrev HasPointwiseLeftDerivedFunctor := ∀ (X : C), F.HasPointwiseLeftDerivedFunctorAt W X

lemma hasPointwiseLeftDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseLeftDerivedFunctorAt W X ↔
      HasPointwiseRightKanExtensionAt L F (L.obj X) := by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h ↦ h.hasLimit', fun h ↦ ⟨h⟩⟩

lemma HasPointwiseLeftDerivedFunctorAt.hasLimit
    [L.IsLocalization W] (X : C) [F.HasPointwiseLeftDerivedFunctorAt W X] :
    HasPointwiseRightKanExtensionAt L F (L.obj X) := by
  rwa [← hasPointwiseLeftDerivedFunctorAt_iff F L W]

lemma hasPointwiseLeftDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) :
    F.HasPointwiseLeftDerivedFunctorAt W X ↔
      F.HasPointwiseLeftDerivedFunctorAt W Y := by
  simp only [F.hasPointwiseLeftDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseRightKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

variable [F.HasPointwiseLeftDerivedFunctor W]

lemma hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor [L.IsLocalization W] :
    HasPointwiseRightKanExtension L F := fun Y ↦ by
  have := Localization.essSurj L W
  rw [← hasPointwiseRightKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y),
    ← F.hasPointwiseLeftDerivedFunctorAt_iff L W]
  infer_instance

lemma hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor :
    F.HasLeftDerivedFunctor W where
  hasRightKanExtension' := by
    have := F.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor W.Q W
    infer_instance

attribute [instance] hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor

variable {F L}

noncomputable def isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
     [L.IsLocalization W] [F'.IsLeftDerivedFunctor α W] :
    (RightExtension.mk _ α).IsPointwiseRightKanExtension :=
  have := hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor F L
  have := IsLeftDerivedFunctor.isRightKanExtension F' α W
  isPointwiseRightKanExtensionOfIsRightKanExtension F' α

end

variable {F L}

set_option backward.isDefEq.respectTransparency false in

def isPointwiseRightKanExtensionAtOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] (Y : C) :
    (RightExtension.mk _ e.inv).IsPointwiseRightKanExtensionAt (L.obj Y) where
  lift s := s.π.app (StructuredArrow.mk (𝟙 (L.obj Y))) ≫ e.hom.app Y
  fac s j := by
    refine Localization.induction_structuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ ↦ ?_) (fun X₁ X₂ w hw φ hφ ↦ ?_) j
    · have eq := s.π.naturality
        (StructuredArrow.homMk f : StructuredArrow.mk φ ⟶ StructuredArrow.mk (φ ≫ L.map f))
      dsimp at eq hφ ⊢
      rw [id_comp] at eq
      rw [assoc] at hφ
      simp [eq, ← reassoc_of% hφ, ← e.inv.naturality f]
    · have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      have eq := s.π.naturality (StructuredArrow.homMk w :
          StructuredArrow.mk (φ ≫ (Localization.isoOfHom L W w hw).inv) ⟶
            StructuredArrow.mk φ)
      dsimp at eq hφ ⊢
      rw [id_comp] at eq
      rw [assoc] at hφ
      simp only [← cancel_mono (F.map w), ← eq, comp_obj, comp_map, assoc,
        ← hφ, ← NatTrans.naturality, ← G.map_comp_assoc,
        Localization.isoOfHom_inv_hom_id, comp_id]
  uniq s m hm := by
    have := hm (StructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at this m hm ⊢
    simp [← reassoc_of% this]

noncomputable def isPointwiseRightKanExtensionOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] :
    (RightExtension.mk _ e.inv).IsPointwiseRightKanExtension := fun Y ↦
  have := Localization.essSurj L W
  (RightExtension.mk _ e.inv).isPointwiseRightKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseRightKanExtensionAtOfIsoOfIsLocalization W e _)

noncomputable def RightExtension.isPointwiseRightKanExtensionOfIsIsoOfIsLocalization
    (E : RightExtension L F) [IsIso E.hom] [L.IsLocalization W] :
    E.IsPointwiseRightKanExtension :=
  Functor.isPointwiseRightKanExtensionOfIsoOfIsLocalization W (asIso E.hom).symm

lemma hasPointwiseLeftDerivedFunctor_of_inverts
    (F : C ⥤ H) {W : MorphismProperty C} (hF : W.IsInvertedBy F) :
    F.HasPointwiseLeftDerivedFunctor W := by
  intro X
  rw [hasPointwiseLeftDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseRightKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseRightKanExtension _

lemma isLeftDerivedFunctor_of_inverts
    [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙ F' ≅ F) :
    F'.IsLeftDerivedFunctor e.hom W where
  isRightKanExtension :=
    (isPointwiseRightKanExtensionOfIsoOfIsLocalization W e.symm).isRightKanExtension

-- INSTANCE (free from Core): [L.IsLocalization

variable {W} in

lemma isIso_of_isLeftDerivedFunctor_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (hF : W.IsInvertedBy F) [LF.IsLeftDerivedFunctor α W] :
    IsIso α := by
  have : α = whiskerLeft _ (leftDerivedUnique _ _ (Localization.fac F hF L).hom α W).inv ≫
      (Localization.fac F hF L).hom := by simp
  rw [this]
  infer_instance

variable {W} in

lemma isLeftDerivedFunctor_iff_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (hF : W.IsInvertedBy F) :
    LF.IsLeftDerivedFunctor α W ↔ IsIso α :=
  ⟨fun _ ↦ isIso_of_isLeftDerivedFunctor_of_inverts LF α hF, fun _ ↦
    isLeftDerivedFunctor_of_inverts W LF (asIso α)⟩

end

end Functor

end CategoryTheory
