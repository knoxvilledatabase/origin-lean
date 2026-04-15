/-
Extracted from Algebra/Category/ModuleCat/Sheaf/Limits.lean
Genuine: 1 of 16 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core

/-! # Limits in categories of sheaves of modules

In this file, it is shown that under suitable assumptions,
limits exist in the category `SheafOfModules R`.

## TODO
* do the same for colimits (which requires constructing the associated sheaf of modules functor)

-/

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Category Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ RingCat.{u}}
  {F : D ⥤ PresheafOfModules.{v} R}
  [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ forget _).sections]
  {c : Cone F}
  [HasLimitsOfShape D AddCommGrpCat.{v}]

lemma isSheaf_of_isLimit (hc : IsLimit c) (hF : ∀ j, Presheaf.IsSheaf J (F.obj j).presheaf) :
    Presheaf.IsSheaf J (c.pt.presheaf) := by
  let G : D ⥤ Sheaf J AddCommGrpCat.{v} :=
    { obj := fun j => ⟨(F.obj j).presheaf, hF j⟩
      map := fun φ => ⟨(PresheafOfModules.toPresheaf R).map (F.map φ)⟩ }
  exact Sheaf.isSheaf_of_isLimit G _ (isLimitOfPreserves (toPresheaf R) hc)

end PresheafOfModules

namespace SheafOfModules

variable {R : Sheaf J RingCat.{u}}

section Limits

variable (F : D ⥤ SheafOfModules.{v} R)
  [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ CategoryTheory.forget _).sections]
  [HasLimitsOfShape D AddCommGrpCat.{v}]

-- INSTANCE (free from Core): (X

-- INSTANCE (free from Core): createsLimit

-- INSTANCE (free from Core): hasLimit

-- INSTANCE (free from Core): evaluationPreservesLimit

end Limits

variable (R D)

section Small

variable [Small.{v} D]

-- INSTANCE (free from Core): hasLimitsOfShape

-- INSTANCE (free from Core): evaluationPreservesLimitsOfShape

-- INSTANCE (free from Core): forgetPreservesLimitsOfShape

end Small

namespace Finite

-- INSTANCE (free from Core): hasFiniteLimits

-- INSTANCE (free from Core): evaluationPreservesFiniteLimits

-- INSTANCE (free from Core): forgetPreservesFiniteLimits

end Finite

-- INSTANCE (free from Core): hasLimitsOfSize

-- INSTANCE (free from Core): evaluationPreservesLimitsOfSize

-- INSTANCE (free from Core): forgetPreservesLimitsOfSize

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end SheafOfModules
