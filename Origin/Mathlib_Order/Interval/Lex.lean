/-
Extracted from Order/Interval/Lex.lean
Genuine: 4 of 11 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

meta import Mathlib.Order.Interval.Basic  -- shake: keep (for `#eval` testing)

meta import Mathlib.Order.Lex  -- shake: keep (for `#eval` testing)

/-!
# The lexicographic order on intervals

This order is compatible with the inclusion ordering, but is total.

Under this ordering, `[(3, 3), (2, 2), (2, 3), (1, 1), (1, 2), (1, 3)]` is sorted.
-/

namespace NonemptyInterval

variable {α}

section LELT

variable [LT α] [LE α]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

theorem toLex_le_toLex {x y : NonemptyInterval α} :
    toLex x ≤ toLex y ↔ y.fst < x.fst ∨ x.fst = y.fst ∧ x.snd ≤ y.snd :=
  Prod.lex_def

theorem toLex_lt_toLex {x y : NonemptyInterval α} :
    toLex x < toLex y ↔ y.fst < x.fst ∨ x.fst = y.fst ∧ x.snd < y.snd :=
  Prod.lex_def

-- INSTANCE (free from Core): [DecidableEq

-- INSTANCE (free from Core): [DecidableEq

#guard_msgs in

#eval [

  NonemptyInterval.mk (1, 1) (by grind),

  NonemptyInterval.mk (1, 2) (by grind),

  NonemptyInterval.mk (1, 3) (by grind),

  NonemptyInterval.mk (2, 2) (by grind),

  NonemptyInterval.mk (2, 3) (by grind),

  NonemptyInterval.mk (3, 3) (by grind)].map toLex |>.mergeSort.map (·.toProd)

end LELT

-- INSTANCE (free from Core): [Preorder

theorem toLex_mono [PartialOrder α] : Monotone (toLex : NonemptyInterval α → _) :=
  Prod.Lex.toLex_mono.comp toDualProd_mono

theorem toLex_strictMono [PartialOrder α] : StrictMono (toLex : NonemptyInterval α → _) :=
  Prod.Lex.toLex_strictMono.comp toDualProd_strictMono

-- INSTANCE (free from Core): [PartialOrder

-- INSTANCE (free from Core): [LinearOrder

end NonemptyInterval
