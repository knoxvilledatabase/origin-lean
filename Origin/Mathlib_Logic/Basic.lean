/-
Extracted from Logic/Basic.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Basic logic properties

This file is one of the earliest imports in mathlib.

## Implementation notes

Theorems that require decidability hypotheses are in the namespace `Decidable`.
Classical versions are in the namespace `Classical`.
-/

open Function

section Miscellany

abbrev hidden {α : Sort*} {a : α} := a

variable {α : Sort*}

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): [Subsingleton

theorem congr_heq {α β γ : Sort _} {f : α → γ} {g : β → γ} {x : α} {y : β}
    (h₁ : f ≍ g) (h₂ : x ≍ y) : f x = g y := by
  cases h₂; cases h₁; rfl

theorem congr_arg_heq {β : α → Sort*} (f : ∀ a, β a) :
    ∀ {a₁ a₂ : α}, a₁ = a₂ → f a₁ ≍ f a₂
  | _, _, rfl => HEq.rfl

theorem dcongr_heq.{u, v}
    {α₁ α₂ : Sort u}
    {β₁ : α₁ → Sort v} {β₂ : α₂ → Sort v}
    {f₁ : ∀ a, β₁ a} {f₂ : ∀ a, β₂ a}
    {a₁ : α₁} {a₂ : α₂}
    (hargs : a₁ ≍ a₂)
    (ht : ∀ t₁ t₂, t₁ ≍ t₂ → β₁ t₁ = β₂ t₂)
    (hf : α₁ = α₂ → β₁ ≍ β₂ → f₁ ≍ f₂) :
    f₁ a₁ ≍ f₂ a₂ := by
  cases hargs
  cases funext fun v => ht v v .rfl
  cases hf rfl .rfl
  rfl
