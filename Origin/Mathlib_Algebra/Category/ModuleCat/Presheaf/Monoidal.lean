/-
Extracted from Algebra/Category/ModuleCat/Presheaf/Monoidal.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

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

open CategoryTheory MonoidalCategory BraidedCategory Category Limits

universe v u v₁ u₁

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

-- INSTANCE (free from Core): (X

namespace PresheafOfModules

namespace Monoidal

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

set_option backward.isDefEq.respectTransparency false in

noncomputable def tensorObjMap {X Y : Cᵒᵖ} (f : X ⟶ Y) : M₁.obj X ⊗ M₂.obj X ⟶
    (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y) :=
  ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ ↦ M₁.map f m₁ ⊗ₜ M₂.map f m₂)
    (by
      intro m₁ m₁' m₂
      dsimp +instances
      rw [map_add, TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by
      intro m₁ m₂ m₂'
      dsimp +instances
      rw [map_add, TensorProduct.tmul_add])
    (by intro a m₁ m₂; dsimp; erw [M₂.map_smul, TensorProduct.tmul_smul (r := R.map f a)]; rfl)

set_option backward.isDefEq.respectTransparency false in
