/-
Extracted from Algebra/Order/Floor/Semiring.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas on `Nat.floor` and `Nat.ceil` for semirings

This file contains basic results on the natural-valued floor and ceiling functions.

## TODO

`LinearOrderedSemiring` can be relaxed to `OrderedSemiring` in many lemmas.

## Tags

rounding, floor, ceil
-/

assert_not_exists Finset

open Set

variable {R K : Type*}

namespace Nat

section LinearOrderedSemiring

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

section floor

theorem floor_lt (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff ha

theorem floor_lt_one (ha : 0 ≤ a) : ⌊a⌋₊ < 1 ↔ a < 1 :=
  (floor_lt ha).trans <| by rw [Nat.cast_one]

theorem floor_le (ha : 0 ≤ a) : (⌊a⌋₊ : R) ≤ a :=
  (le_floor_iff ha).1 le_rfl

theorem floor_eq_iff (ha : 0 ≤ a) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff ha, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt ha, Nat.lt_add_one_iff,
    le_antisymm_iff, and_comm]

variable [IsStrictOrderedRing R]

theorem lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n :=
  lt_of_not_ge fun h' => (le_floor h').not_gt h

theorem lt_one_of_floor_lt_one (h : ⌊a⌋₊ < 1) : a < 1 := mod_cast lt_of_floor_lt h

theorem lt_succ_floor (a : R) : a < ⌊a⌋₊.succ :=
  lt_of_floor_lt <| Nat.lt_succ_self _
