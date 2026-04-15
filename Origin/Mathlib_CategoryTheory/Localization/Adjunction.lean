/-
Extracted from CategoryTheory/Localization/Adjunction.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.CatCommSq
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Localization of adjunctions

In this file, we show that if we have an adjunction `adj : G ⊣ F` such that both
functors `G : C₁ ⥤ C₂` and `F : C₂ ⥤ C₁` induce functors
`G' : D₁ ⥤ D₂` and `F' : D₂ ⥤ D₁` on localized categories, i.e. that we
have localization functors `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` with respect
to morphism properties `W₁` and `W₂` respectively, and 2-commutative diagrams
`[CatCommSq G L₁ L₂ G']` and `[CatCommSq F L₂ L₁ F']`, then we have an
induced adjunction `Adjunction.localization L₁ W₁ L₂ W₂ G' F' : G' ⊣ F'`.

-/

namespace CategoryTheory

open Localization Category

namespace Adjunction

variable {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)

section

variable (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (G' : D₁ ⥤ D₂) (F' : D₂ ⥤ D₁)
  [CatCommSq G L₁ L₂ G'] [CatCommSq F L₂ L₁ F']

namespace Localization

noncomputable def ε : 𝟭 D₁ ⟶ G' ⋙ F' := by
  letI : Lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    Lifting.mk (CatCommSq.hComp G F L₁ L₂ L₁ G' F').iso'.symm
  exact Localization.liftNatTrans L₁ W₁ L₁ ((G ⋙ F) ⋙ L₁) (𝟭 D₁) (G' ⋙ F')
    (whiskerRight adj.unit L₁)

lemma ε_app (X₁ : C₁) :
    (ε adj L₁ W₁ L₂ G' F').app (L₁.obj X₁) =
      L₁.map (adj.unit.app X₁) ≫ (CatCommSq.iso F L₂ L₁ F').hom.app (G.obj X₁) ≫
        F'.map ((CatCommSq.iso G L₁ L₂ G').hom.app X₁) := by
  letI : Lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    Lifting.mk (CatCommSq.hComp G F L₁ L₂ L₁ G' F').iso'.symm
  simp only [ε, liftNatTrans_app, Lifting.iso, Iso.symm,
    Functor.id_obj, Functor.comp_obj, Lifting.id_iso', Functor.rightUnitor_hom_app,
      whiskerRight_app, CatCommSq.hComp_iso'_hom_app, id_comp]

noncomputable def η : F' ⋙ G' ⟶ 𝟭 D₂ := by
  letI : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso'.symm
  exact liftNatTrans L₂ W₂ ((F ⋙ G) ⋙ L₂) L₂ (F' ⋙ G') (𝟭 D₂) (whiskerRight adj.counit L₂)

lemma η_app (X₂ : C₂) :
    (η adj L₁ L₂ W₂ G' F').app (L₂.obj X₂) =
      G'.map ((CatCommSq.iso F L₂ L₁ F').inv.app X₂) ≫
        (CatCommSq.iso G L₁ L₂ G').inv.app (F.obj X₂) ≫
        L₂.map (adj.counit.app X₂) := by
  letI : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso'.symm
  simp only [η, liftNatTrans_app, Lifting.iso, Iso.symm, CatCommSq.hComp_iso'_inv_app,
    whiskerRight_app, Lifting.id_iso', Functor.rightUnitor_inv_app, comp_id, assoc]

end Localization

noncomputable def localization : G' ⊣ F' :=
  Adjunction.mkOfUnitCounit
    { unit := Localization.ε adj L₁ W₁ L₂ G' F'
      counit := Localization.η adj L₁ L₂ W₂ G' F'
      left_triangle := by
        apply natTrans_ext L₁ W₁
        intro X₁
        have eq := congr_app adj.left_triangle X₁
        dsimp at eq
        rw [NatTrans.comp_app, NatTrans.comp_app, whiskerRight_app, Localization.ε_app,
          Functor.associator_hom_app, id_comp, whiskerLeft_app, G'.map_comp, G'.map_comp,
          assoc, assoc]
        erw [(Localization.η adj L₁ L₂ W₂ G' F').naturality, Localization.η_app,
          assoc, assoc, ← G'.map_comp_assoc, ← G'.map_comp_assoc, assoc, Iso.hom_inv_id_app,
          comp_id, (CatCommSq.iso G L₁ L₂ G').inv.naturality_assoc, ← L₂.map_comp_assoc, eq,
          L₂.map_id, id_comp, Iso.inv_hom_id_app]
        rfl
      right_triangle := by
        apply natTrans_ext L₂ W₂
        intro X₂
        have eq := congr_app adj.right_triangle X₂
        dsimp at eq
        rw [NatTrans.comp_app, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
          Localization.η_app, Functor.associator_inv_app, id_comp, F'.map_comp, F'.map_comp]
        erw [← (Localization.ε _ _ _ _ _ _).naturality_assoc, Localization.ε_app,
          assoc, assoc, ← F'.map_comp_assoc, Iso.hom_inv_id_app, F'.map_id, id_comp,
          ← NatTrans.naturality, ← L₁.map_comp_assoc, eq, L₁.map_id, id_comp,
          Iso.inv_hom_id_app]
        rfl }

@[simp]
lemma localization_unit_app (X₁ : C₁) :
    (adj.localization L₁ W₁ L₂ W₂ G' F').unit.app (L₁.obj X₁) =
    L₁.map (adj.unit.app X₁) ≫ (CatCommSq.iso F L₂ L₁ F').hom.app (G.obj X₁) ≫
      F'.map ((CatCommSq.iso G L₁ L₂ G').hom.app X₁) := by
  apply Localization.ε_app

@[simp]
lemma localization_counit_app (X₂ : C₂) :
    (adj.localization L₁ W₁ L₂ W₂ G' F').counit.app (L₂.obj X₂) =
    G'.map ((CatCommSq.iso F L₂ L₁ F').inv.app X₂) ≫
      (CatCommSq.iso G L₁ L₂ G').inv.app (F.obj X₂) ≫
      L₂.map (adj.counit.app X₂) := by
  apply Localization.η_app

end

include adj in

lemma isLocalization [F.Full] [F.Faithful] :
    G.IsLocalization ((MorphismProperty.isomorphisms C₂).inverseImage G) := by
  let W := ((MorphismProperty.isomorphisms C₂).inverseImage G)
  have hG : W.IsInvertedBy G := fun _ _ _ hf => hf
  have : ∀ (X : C₁), IsIso ((whiskerRight adj.unit W.Q).app X) := fun X =>
    Localization.inverts W.Q W _ (by
      change IsIso _
      infer_instance)
  have : IsIso (whiskerRight adj.unit W.Q) := NatIso.isIso_of_isIso_app _
  let e : W.Localization ≌ C₂ := Equivalence.mk (Localization.lift G hG W.Q) (F ⋙ W.Q)
    (liftNatIso W.Q W W.Q (G ⋙ F ⋙ W.Q) _ _
    (W.Q.leftUnitor.symm ≪≫ asIso (whiskerRight adj.unit W.Q)))
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Localization.fac G hG W.Q) ≪≫
      asIso adj.counit)
  apply Functor.IsLocalization.of_equivalence_target W.Q W G e
    (Localization.fac G hG W.Q)

end Adjunction

end CategoryTheory
