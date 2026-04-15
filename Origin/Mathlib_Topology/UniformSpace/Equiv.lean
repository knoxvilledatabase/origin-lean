/-
Extracted from Topology/UniformSpace/Equiv.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Uniform isomorphisms

This file defines uniform isomorphisms between two uniform spaces. They are bijections with both
directions uniformly continuous. We denote uniform isomorphisms with the notation `≃ᵤ`.

## Main definitions

* `UniformEquiv α β`: The type of uniform isomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ᵤ β`.

-/

open Set Filter

universe u v

variable {α : Type u} {β : Type*} {γ : Type*} {δ : Type*}

structure UniformEquiv (α : Type*) (β : Type*) [UniformSpace α] [UniformSpace β] extends
  α ≃ β where
  /-- Uniform continuity of the function -/
  uniformContinuous_toFun : UniformContinuous toFun
  /-- Uniform continuity of the inverse -/
  uniformContinuous_invFun : UniformContinuous invFun

infixl:25 " ≃ᵤ " => UniformEquiv

namespace UniformEquiv

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]

theorem toEquiv_injective : Function.Injective (toEquiv : α ≃ᵤ β → α ≃ β)
  | ⟨e, h₁, h₂⟩, ⟨e', h₁', h₂'⟩, h => by simpa only [mk.injEq]

-- INSTANCE (free from Core): :
