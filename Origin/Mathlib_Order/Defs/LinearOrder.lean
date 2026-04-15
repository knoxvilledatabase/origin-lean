/-
Extracted from Order/Defs/LinearOrder.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Orders

Defines classes for linear orders and proves some basic lemmas about them.

We intentionally avoid using `grind` in this fundamental file to keep the proofs understandable,
rather than hiding the reasoning behind automation.
-/

variable {α : Type*}

section LinearOrder

/-!
### Definition of `LinearOrder` and lemmas about types with a linear order
-/

def maxDefault [LE α] [DecidableLE α] (a b : α) :=
  if a ≤ b then b else a

def minDefault [LE α] [DecidableLE α] (a b : α) :=
  if a ≤ b then a else b

macro "compareOfLessAndEq_rfl" : tactic =>

  `(tactic| (intro a b; first | rfl |

    (simp only [compare, compareOfLessAndEq]; split_ifs <;> rfl) |

    (induction a <;> induction b <;> simp +decide only)))

class LinearOrder (α : Type*) extends PartialOrder α, Min α, Max α, Ord α where
  /-- A linear order is total. -/
  protected le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  /-- The minimum function is equivalent to the one you get from `minOfLe`. -/
  protected min_def : ∀ a b, min a b = if a ≤ b then a else b := by intros; rfl
  /-- The minimum function is equivalent to the one you get from `maxOfLe`. -/
  protected max_def : ∀ a b, max a b = if a ≤ b then b else a := by intros; rfl
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl

attribute [to_dual existing] LinearOrder.toMax

variable [LinearOrder α] {a b c : α}

-- INSTANCE (free from Core): 900]

-- INSTANCE (free from Core): 900]

-- INSTANCE (free from Core): 900]

-- INSTANCE (free from Core): :
