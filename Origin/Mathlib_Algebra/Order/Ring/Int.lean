/-
Extracted from Algebra/Order/Ring/Int.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The integers form a linear ordered ring

This file contains:
* instances on `ℤ`. The stronger one is `Int.instLinearOrderedCommRing`.
* basic lemmas about integers that involve order properties.

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

assert_not_exists Set.Subsingleton

open Function Nat

namespace Int

-- INSTANCE (free from Core): instIsStrictOrderedRing

/-! ### Miscellaneous lemmas -/

lemma isCompl_even_odd : IsCompl { n : ℤ | Even n } { n | Odd n } := by
  simp [← not_even_iff_odd, ← Set.compl_setOf, isCompl_compl]
