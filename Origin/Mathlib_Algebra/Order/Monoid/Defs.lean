/-
Extracted from Algebra/Order/Monoid/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordered monoids

This file provides the definitions of ordered monoids.

-/

open Function

variable {α : Type*}

class IsOrderedAddMonoid (α : Type*) [AddCommMonoid α] [Preorder α] where
  protected add_le_add_left (a b : α) : a ≤ b → ∀ c, a + c ≤ b + c
  protected add_le_add_right (a b : α) : a ≤ b → ∀ c, c + a ≤ c + b := fun h c ↦ by
    rw [add_comm c, add_comm c]; exact add_le_add_left a b h c
