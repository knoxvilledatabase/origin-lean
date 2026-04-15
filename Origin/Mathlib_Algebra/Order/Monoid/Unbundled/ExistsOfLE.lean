/-
Extracted from Algebra/Order/Monoid/Unbundled/ExistsOfLE.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Unbundled and weaker forms of canonically ordered monoids

This file provides a Prop-valued mixin for monoids satisfying a one-sided cancellativity property,
namely that there is some `c` such that `b = a + c` if `a ≤ b`. This is particularly useful for
generalising statements from groups/rings/fields that don't mention negation or subtraction to
monoids/semirings/semifields.
-/

universe u

variable {α : Type u}

class ExistsAddOfLE (α : Type u) [Add α] [LE α] : Prop where
  /-- For `a ≤ b`, there is a `c` so `b = a + c`. -/
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a + c
