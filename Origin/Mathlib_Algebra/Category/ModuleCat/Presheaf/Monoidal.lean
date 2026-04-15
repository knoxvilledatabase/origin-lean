/-
Extracted from Algebra/Category/ModuleCat/Presheaf/Monoidal.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# The monoidal category structure on presheaves of modules

Given a presheaf of commutative rings `R : Cᵒᵖ ⥤ CommRingCat`, we construct
the monoidal category structure on the category of presheaves of modules
`PresheafOfModules (R ⋙ forget₂ _ _)`. The tensor product `M₁ ⊗ M₂` is defined
as the presheaf of modules which sends `X : Cᵒᵖ` to `M₁.obj X ⊗ M₂.obj X`.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

open CategoryTheory MonoidalCategory Category

universe v u v₁ u₁

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

instance (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ _ RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

namespace PresheafOfModules

namespace Monoidal

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

noncomputable def tensorObjMap {X Y : Cᵒᵖ} (f : X ⟶ Y) : M₁.obj X ⊗ M₂.obj X ⟶
    (ModuleCat.restrictScalars (R.map f)).obj (M₁.obj Y ⊗ M₂.obj Y) :=
  ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ ↦ M₁.map f m₁ ⊗ₜ M₂.map f m₂)
    (by intro m₁ m₁' m₂; dsimp; rw [map_add, TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by intro m₁ m₂ m₂'; dsimp; rw [map_add, TensorProduct.tmul_add])
    (by intro a m₁ m₂; dsimp; erw [M₂.map_smul, TensorProduct.tmul_smul (r := R.map f a)]; rfl)

@[simps obj]
noncomputable def tensorObj : PresheafOfModules (R ⋙ forget₂ _ _) where
  obj X := M₁.obj X ⊗ M₂.obj X
  map f := tensorObjMap M₁ M₂ f
  map_id X := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m₁ m₂
    dsimp [tensorObjMap]
    simp only [map_id, Functor.comp_obj, CommRingCat.forgetToRingCat_obj, Functor.comp_map,
      ModuleCat.restrictScalarsId'_inv_app, ModuleCat.restrictScalarsId'App_inv_apply]
    rfl)
  map_comp f g := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m₁ m₂
    dsimp [tensorObjMap]
    simp only [map_comp, Functor.comp_obj, CommRingCat.forgetToRingCat_obj, Functor.comp_map,
      ModuleCat.restrictScalarsComp'_inv_app, ModuleCat.coe_comp, Function.comp_apply,
      ModuleCat.restrictScalars.map_apply, ModuleCat.restrictScalarsComp'App_inv_apply]
    rfl)

variable {M₁ M₂ M₃ M₄}

@[simp]
lemma tensorObj_map_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    DFunLike.coe (α := (M₁.obj X ⊗ M₂.obj X : _))
      (β := fun _ ↦ (ModuleCat.restrictScalars
        ((forget₂ CommRingCat RingCat).map (R.map f))).obj (M₁.obj Y ⊗ M₂.obj Y))
      ((tensorObj M₁ M₂).map f) (m₁ ⊗ₜ[R.obj X] m₂) = M₁.map f m₁ ⊗ₜ[R.obj Y] M₂.map f m₂ := rfl

@[simps]
noncomputable def tensorHom (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) : tensorObj M₁ M₃ ⟶ tensorObj M₂ M₄ where
  app X := f.app X ⊗ g.app X
  naturality {X Y} φ := ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₃ ↦ by
    dsimp
    rw [tensorObj_map_tmul]
    erw [ModuleCat.MonoidalCategory.tensorHom_tmul, tensorObj_map_tmul,
      naturality_apply, naturality_apply]
    rfl)

end Monoidal

open Monoidal

open ModuleCat.MonoidalCategory in

noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  tensorObj := tensorObj
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom := tensorHom
  tensorUnit := unit _
  associator M₁ M₂ M₃ := isoMk (fun _ ↦ α_ _ _ _)
    (fun _ _ _ ↦ ModuleCat.MonoidalCategory.tensor_ext₃' (by intros; rfl))
  leftUnitor M := Iso.symm (isoMk (fun _ ↦ (λ_ _).symm) (fun X Y f ↦ by
    ext m
    dsimp
    erw [leftUnitor_inv_apply, leftUnitor_inv_apply, tensorObj_map_tmul, (R.map f).map_one]
    rfl))
  rightUnitor M := Iso.symm (isoMk (fun _ ↦ (ρ_ _).symm) (fun X Y f ↦ by
    ext m
    dsimp
    erw [rightUnitor_inv_apply, rightUnitor_inv_apply, tensorObj_map_tmul, (R.map f).map_one]
    rfl))

noncomputable instance monoidalCategory :
    MonoidalCategory (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  tensorHom_def _ _ := by ext1; apply tensorHom_def
  tensor_id _ _ := by ext1; apply tensor_id
  tensor_comp _ _ _ _ := by ext1; apply tensor_comp
  whiskerLeft_id M₁ M₂ := by
    ext1 X
    apply MonoidalCategory.whiskerLeft_id (C := ModuleCat (R.obj X))
  id_whiskerRight _ _ := by
    ext1 X
    apply MonoidalCategory.id_whiskerRight (C := ModuleCat (R.obj X))
  associator_naturality _ _ _ := by ext1; apply associator_naturality
  leftUnitor_naturality _ := by ext1; apply leftUnitor_naturality
  rightUnitor_naturality _ := by ext1; apply rightUnitor_naturality
  pentagon _ _ _ _ := by ext1; apply pentagon
  triangle _ _ := by ext1; apply triangle

end PresheafOfModules
