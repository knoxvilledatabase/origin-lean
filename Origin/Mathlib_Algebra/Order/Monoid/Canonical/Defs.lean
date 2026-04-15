/-
Extracted from Algebra/Order/Monoid/Canonical/Defs.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Canonically ordered monoids
-/

universe u

variable {α : Type u}

class CanonicallyOrderedAdd (α : Type*) [Add α] [LE α] : Prop
    extends ExistsAddOfLE α where
  /-- For any `a` and `b`, `a ≤ a + b` -/
  protected le_add_self : ∀ a b : α, a ≤ b + a
  protected le_self_add : ∀ a b : α, a ≤ a + b

-- INSTANCE (free from Core): 50]
