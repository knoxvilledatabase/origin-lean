/-
Extracted from Data/Prod/PProd.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extra facts about `PProd`
-/

open Function

variable {α β γ δ : Sort*}

namespace PProd

def mk.injArrow {α : Type*} {β : Type*} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort*⦄, (x₁ = x₂ → y₁ = y₂ → P) → P := by
  intros h P w
  cases h
  exact w rfl rfl
