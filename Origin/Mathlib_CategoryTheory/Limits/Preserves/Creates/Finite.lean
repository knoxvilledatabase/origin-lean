/-
Extracted from CategoryTheory/Limits/Preserves/Creates/Finite.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Creation of finite limits

This file defines the classes `CreatesFiniteLimits`, `CreatesFiniteColimits`,
`CreatesFiniteProducts` and `CreatesFiniteCoproducts`.
-/

namespace CategoryTheory.Limits

universe w w' v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

class CreatesFiniteLimits (F : C ⥤ D) where
  /-- `F` creates all finite limits. -/
  createsFiniteLimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], CreatesLimitsOfShape J F := by infer_instance

attribute [instance_reducible, instance] CreatesFiniteLimits.createsFiniteLimits

noncomputable section

-- INSTANCE (free from Core): (priority
