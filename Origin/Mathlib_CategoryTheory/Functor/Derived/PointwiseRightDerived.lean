/-
Extracted from CategoryTheory/Functor/Derived/PointwiseRightDerived.lean
Genuine: 15 of 16 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Pointwise right derived functors

We define pointwise right derived functors using the notion
of pointwise left Kan extensions.

We show that if `F : C ⥤ H` inverts `W : MorphismProperty C`,
then it has a pointwise right derived functor.

Note: the file `Mathlib/CategoryTheory/Functor/Derived/PointwiseLeftDerived.lean` was obtained
by dualizing this file. These two files should be kept in sync.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
  (F' : D ⥤ H) (F : C ⥤ H) (L : C ⥤ D) (α : F ⟶ L ⋙ F') (W : MorphismProperty C)

class HasPointwiseRightDerivedFunctorAt (X : C) : Prop where
  /-- Use the more general `hasColimit` lemma instead, see also
  `hasPointwiseRightDerivedFunctorAt_iff` -/
  hasColimit' : HasPointwiseLeftKanExtensionAt W.Q F (W.Q.obj X)

abbrev HasPointwiseRightDerivedFunctor := ∀ (X : C), F.HasPointwiseRightDerivedFunctorAt W X

lemma hasPointwiseRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      HasPointwiseLeftKanExtensionAt L F (L.obj X) := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h ↦ h.hasColimit', fun h ↦ ⟨h⟩⟩

lemma HasPointwiseRightDerivedFunctorAt.hasColimit
    [L.IsLocalization W] (X : C) [F.HasPointwiseRightDerivedFunctorAt W X] :
    HasPointwiseLeftKanExtensionAt L F (L.obj X) := by
  rwa [← hasPointwiseRightDerivedFunctorAt_iff F L W]

lemma hasPointwiseRightDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      F.HasPointwiseRightDerivedFunctorAt W Y := by
  simp only [F.hasPointwiseRightDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseLeftKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

variable [F.HasPointwiseRightDerivedFunctor W]

lemma hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor [L.IsLocalization W] :
    HasPointwiseLeftKanExtension L F := fun Y ↦ by
  have := Localization.essSurj L W
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y),
    ← F.hasPointwiseRightDerivedFunctorAt_iff L W]
  infer_instance

lemma hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor :
    F.HasRightDerivedFunctor W where
  hasLeftKanExtension' := by
    have := F.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor W.Q W
    infer_instance

attribute [instance] hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor

variable {F L}

noncomputable def isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
     [L.IsLocalization W] [F'.IsRightDerivedFunctor α W] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
  have := hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor F L
  have := IsRightDerivedFunctor.isLeftKanExtension F' α W
  isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α

end

variable {F L}

set_option backward.isDefEq.respectTransparency false in

def isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] (Y : C) :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtensionAt (L.obj Y) where
  desc s := e.inv.app Y ≫ s.ι.app (CostructuredArrow.mk (𝟙 (L.obj Y)))
  fac s j := by
    refine Localization.induction_costructuredArrow L W _ (by simp)
      (fun X₁ X₂ f φ hφ ↦ ?_) (fun X₁ X₂ w hw φ hφ ↦ ?_) j
    · have eq := s.ι.naturality
        (CostructuredArrow.homMk f : CostructuredArrow.mk (L.map f ≫ φ) ⟶ CostructuredArrow.mk φ)
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [assoc, map_comp_assoc, ← eq, ← hφ, NatTrans.naturality_assoc, comp_map]
    · have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      have eq := s.ι.naturality
        (CostructuredArrow.homMk w : CostructuredArrow.mk φ ⟶ CostructuredArrow.mk
          ((Localization.isoOfHom L W w hw).inv ≫ φ))
      dsimp at eq hφ ⊢
      rw [comp_id] at eq
      rw [assoc] at hφ
      rw [map_comp, assoc, assoc, ← cancel_epi (F.map w), eq, ← hφ,
        NatTrans.naturality_assoc, comp_map, ← G.map_comp_assoc]
      simp
  uniq s m hm := by
    have := hm (CostructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at this m hm ⊢
    simp only [← this, map_id, comp_id, Iso.inv_hom_id_app_assoc]

noncomputable def isPointwiseLeftKanExtensionOfIsoOfIsLocalization
    {G : D ⥤ H} (e : F ≅ L ⋙ G) [L.IsLocalization W] :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtension := fun Y ↦
  have := Localization.essSurj L W
  (LeftExtension.mk _ e.hom).isPointwiseLeftKanExtensionAtEquivOfIso'
    (L.objObjPreimageIso Y) (isPointwiseLeftKanExtensionAtOfIsoOfIsLocalization W e _)

set_option backward.isDefEq.respectTransparency false in

noncomputable def LeftExtension.isPointwiseLeftKanExtensionOfIsIsoOfIsLocalization
    (E : LeftExtension L F) [IsIso E.hom] [L.IsLocalization W] :
    E.IsPointwiseLeftKanExtension :=
  Functor.isPointwiseLeftKanExtensionOfIsoOfIsLocalization W (asIso E.hom)

lemma hasPointwiseRightDerivedFunctor_of_inverts
    (F : C ⥤ H) {W : MorphismProperty C} (hF : W.IsInvertedBy F) :
    F.HasPointwiseRightDerivedFunctor W := by
  intro X
  rw [hasPointwiseRightDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W
    (Localization.fac F hF W.Q).symm).hasPointwiseLeftKanExtension _

lemma isRightDerivedFunctor_of_inverts
    [L.IsLocalization W] (F' : D ⥤ H) (e : L ⋙ F' ≅ F) :
    F'.IsRightDerivedFunctor e.inv W where
  isLeftKanExtension :=
    (isPointwiseLeftKanExtensionOfIsoOfIsLocalization W e.symm).isLeftKanExtension

-- INSTANCE (free from Core): [L.IsLocalization

variable {W} in

lemma isIso_of_isRightDerivedFunctor_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    (hF : W.IsInvertedBy F) [RF.IsRightDerivedFunctor α W] :
    IsIso α := by
  have : α = (Localization.fac F hF L).inv ≫
    whiskerLeft _ (rightDerivedUnique _ _ (Localization.fac F hF L).inv α W).hom := by simp
  rw [this]
  infer_instance

variable {W} in

lemma isRightDerivedFunctor_iff_of_inverts [L.IsLocalization W]
    {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    (hF : W.IsInvertedBy F) :
    RF.IsRightDerivedFunctor α W ↔ IsIso α :=
  ⟨fun _ ↦ isIso_of_isRightDerivedFunctor_of_inverts RF α hF, fun _ ↦
    isRightDerivedFunctor_of_inverts W RF (asIso α).symm⟩

end

end Functor

end CategoryTheory
