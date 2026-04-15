/-
Extracted from Data/Prod/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extra facts about `Prod`

This file proves various simple lemmas about `Prod`.
It also defines better delaborators for product projections.
-/

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

namespace Prod

lemma swap_eq_iff_eq_swap {x : α × β} {y : β × α} : x.swap = y ↔ x = y.swap := by grind

def mk.injArrow {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort*⦄, (x₁ = x₂ → y₁ = y₂ → P) → P := by
  intros h P w
  cases h
  exact w rfl rfl
