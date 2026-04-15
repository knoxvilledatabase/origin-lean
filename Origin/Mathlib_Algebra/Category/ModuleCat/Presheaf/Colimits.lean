/-
Extracted from Algebra/Category/ModuleCat/Presheaf/Colimits.lean
Genuine: 4 of 14 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Colimits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
colimits exist in the category `PresheafOfModules R`.

-/

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]
  (F : J ⥤ PresheafOfModules.{v} R)

section Colimits

variable [∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), PreservesColimit (F ⋙ evaluation R Y)
  (ModuleCat.restrictScalars (R.map f))]

def evaluationJointlyReflectsColimits (c : Cocone F)
    (hc : ∀ (X : Cᵒᵖ), IsColimit ((evaluation R X).mapCocone c)) : IsColimit c where
  desc s :=
    { app := fun X => (hc X).desc ((evaluation R X).mapCocone s)
      naturality := fun {X Y} f ↦ (hc X).hom_ext (fun j ↦ by
        rw [(hc X).fac_assoc ((evaluation R X).mapCocone s) j]
        have h₁ := (c.ι.app j).naturality f
        have h₂ := (hc Y).fac ((evaluation R Y).mapCocone s)
        dsimp at h₁ h₂ ⊢
        simp only [← reassoc_of% h₁, ← Functor.map_comp, h₂, Hom.naturality]) }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCocone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCocone s)
    intro j
    dsimp
    rw [← hm]
    rfl

variable [∀ X, HasColimit (F ⋙ evaluation R X)]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasColimit (F ⋙ evaluation R Y ⋙ (ModuleCat.restrictScalars (R.map f))) :=
  ⟨_, isColimitOfPreserves (ModuleCat.restrictScalars (R.map f))
    (colimit.isColimit (F ⋙ evaluation R Y))⟩

@[simps]
noncomputable def colimitPresheafOfModules : PresheafOfModules R where
  obj X := colimit (F ⋙ evaluation R X)
  map {_ Y} f := colimMap (whiskerLeft F (restriction R f)) ≫
    (preservesColimitIso (ModuleCat.restrictScalars (R.map f)) (F ⋙ evaluation R Y)).inv
  map_id X := colimit.hom_ext (fun j => by
    dsimp
    rw [ι_colimMap_assoc, whiskerLeft_app, restriction_app]
    erw [ι_preservesColimitIso_inv (G := ModuleCat.restrictScalars (R.map (𝟙 X))),
      ModuleCat.restrictScalarsId'App_inv_naturality]
    rw [map_id]
    dsimp)
  map_comp {X Y Z} f g := colimit.hom_ext (fun j => by
    dsimp
    rw [ι_colimMap_assoc, whiskerLeft_app, restriction_app, assoc, ι_colimMap_assoc]
    erw [ι_preservesColimitIso_inv (G := ModuleCat.restrictScalars (R.map (f ≫ g))),
      ι_preservesColimitIso_inv_assoc (G := ModuleCat.restrictScalars (R.map f))]
    rw [← Functor.map_comp_assoc, ι_colimMap_assoc]
    erw [ι_preservesColimitIso_inv (G := ModuleCat.restrictScalars (R.map g))]
    rw [map_comp, ModuleCat.restrictScalarsComp'_inv_app, assoc, assoc,
      whiskerLeft_app, whiskerLeft_app, restriction_app, restriction_app]
    simp only [Functor.map_comp, assoc]
    rfl)

@[simps]
noncomputable def colimitCocone : Cocone F where
  pt := colimitPresheafOfModules F
  ι :=
    { app := fun j ↦
        { app := fun X ↦ colimit.ι (F ⋙ evaluation R X) j
          naturality := fun {X Y} f ↦ by
            dsimp
            erw [colimit.ι_desc_assoc, assoc, ← ι_preservesColimitIso_inv]
            rfl }
      naturality := fun {X Y} f ↦ by
        ext1 X
        simpa using colimit.w (F ⋙ evaluation R X) f }

noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  evaluationJointlyReflectsColimits _ _ (fun _ => colimit.isColimit _)

instance hasColimit : HasColimit F := ⟨_, isColimitColimitCocone F⟩

instance evaluation_preservesColimit (X : Cᵒᵖ) :
    PreservesColimit F (evaluation R X) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F) (colimit.isColimit _)

variable [∀ X, PreservesColimit F
  (evaluation R X ⋙ forget₂ (ModuleCat (R.obj X)) AddCommGrp)]

instance toPresheaf_preservesColimit :
    PreservesColimit F (toPresheaf R) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (Limits.evaluationJointlyReflectsColimits _
      (fun X => isColimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrp)
        (isColimitColimitCocone F)))

end Colimits

variable (R J)

section HasColimitsOfShape

variable [HasColimitsOfShape J AddCommGrp.{v}]

instance hasColimitsOfShape : HasColimitsOfShape J (PresheafOfModules.{v} R) where

noncomputable instance evaluation_preservesColimitsOfShape (X : Cᵒᵖ) :
    PreservesColimitsOfShape J (evaluation R X : PresheafOfModules.{v} R ⥤ _) where

noncomputable instance toPresheaf_preservesColimitsOfShape :
    PreservesColimitsOfShape J (toPresheaf.{v} R) where

end HasColimitsOfShape

namespace Finite

instance hasFiniteColimits : HasFiniteColimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

noncomputable instance evaluation_preservesFiniteColimits (X : Cᵒᵖ) :
    PreservesFiniteColimits (evaluation.{v} R X) where

noncomputable instance toPresheaf_preservesFiniteColimits :
    PreservesFiniteColimits (toPresheaf R) where

end Finite

end PresheafOfModules
