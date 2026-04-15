/-
Extracted from Data/Rat/Floor.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

meta import Mathlib.Algebra.Order.Floor.Defs

public meta import Mathlib.Algebra.Order.Round

/-!
# Floor Function for Rational Numbers

## Summary

We define the `FloorRing` instance on `ℚ`. Some technical lemmas relating `floor` to integer
division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/

assert_not_exists Finset

open Int

namespace Rat

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

-- INSTANCE (free from Core): :

protected theorem floor_def' {q : ℚ} : ⌊q⌋ = q.num / q.den := Rat.floor_def q

protected theorem ceil_def' (q : ℚ) : ⌈q⌉ = -(-q.num / ↑q.den) := by
  change -⌊-q⌋ = _
  rw [Rat.floor_def', num_neg_eq_neg_num, den_neg_eq_den]
