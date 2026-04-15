/-
Extracted from Algebra/Order/Floor/Ring.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas on `Int.floor`, `Int.ceil` and `Int.fract`

This file contains basic results on the integer-valued floor and ceiling functions, as well as the
fractional part operator.

## TODO

`LinearOrderedRing` can be relaxed to `OrderedRing` in many lemmas.

## Tags

rounding, floor, ceil
-/

assert_not_exists Finset

open Set

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

variable {α : Type*}

theorem int_floor_nonneg [Ring α] [LinearOrder α] [FloorRing α] {a : α} (ha : 0 ≤ a) :
    0 ≤ ⌊a⌋ :=
  Int.floor_nonneg.2 ha

theorem int_floor_nonneg_of_pos [Ring α] [LinearOrder α] [FloorRing α] {a : α}
    (ha : 0 < a) :
    0 ≤ ⌊a⌋ :=
  int_floor_nonneg ha.le
