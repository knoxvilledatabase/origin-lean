/-
Extracted from Data/Rat/Star.lean
Genuine: 2 of 6 | Dissolved: 2 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Star ordered ring structures on `ℚ` and `ℚ≥0`

This file shows that `ℚ` and `ℚ≥0` are `StarOrderedRing`s. In particular, this means that every
nonnegative rational number is a sum of squares.
-/

open AddSubmonoid Set

open scoped NNRat

namespace NNRat

-- DISSOLVED: addSubmonoid_closure_range_pow

@[simp] lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ≥0 ↦ x * x) = ⊤ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero

instance instStarOrderedRing : StarOrderedRing ℚ≥0 where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end NNRat

namespace Rat

-- DISSOLVED: addSubmonoid_closure_range_pow

@[simp]
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ ↦ x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero even_two

instance instStarOrderedRing : StarOrderedRing ℚ where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end Rat
