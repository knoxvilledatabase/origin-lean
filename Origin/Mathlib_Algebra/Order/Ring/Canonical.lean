/-
Extracted from Algebra/Order/Ring/Canonical.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Canonically ordered rings and semirings.
-/

open Function

universe u

variable {R : Type u}

-- INSTANCE (free from Core): (priority

lemma Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [Nontrivial R] {a : R} :
    Odd a → 0 < a := by
  rintro ⟨k, rfl⟩; simp

namespace CanonicallyOrderedAdd

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]

lemma toIsOrderedMonoid : IsOrderedMonoid R where
  mul_le_mul_left _ _ := mul_le_mul_left

lemma toIsOrderedRing : IsOrderedRing R where
  add_le_add_left _ _ := add_le_add_left
