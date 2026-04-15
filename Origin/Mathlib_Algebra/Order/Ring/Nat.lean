/-
Extracted from Algebra/Order/Ring/Nat.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The natural numbers form an ordered semiring

This file contains the commutative linear ordered semiring instance on the natural numbers.

See note [foundational algebra order theory].
-/

namespace Nat

/-! ### Instances -/

-- INSTANCE (free from Core): instIsStrictOrderedRing

-- INSTANCE (free from Core): instLinearOrderedCommMonoidWithZero

/-! ### Miscellaneous lemmas -/

lemma isCompl_even_odd : IsCompl { n : ℕ | Even n } { n | Odd n } := by
  simp only [← Set.compl_setOf, isCompl_compl, ← not_even_iff_odd]

end Nat
