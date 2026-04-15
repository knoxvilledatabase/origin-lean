/-
Extracted from Order/Interval/Finset/Box.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Decomposing a locally finite ordered ring into boxes

This file proves that any locally finite ordered ring can be decomposed into "boxes", namely
differences of consecutive intervals.

## Implementation notes

We don't need the full ring structure, only that there is an order embedding `ℤ → `
-/

/-! ### General locally finite ordered ring -/

namespace Finset

variable {α : Type*} [Ring α] [PartialOrder α] [IsOrderedRing α] [LocallyFiniteOrder α] {n : ℕ}

private lemma Icc_neg_mono : Monotone fun n : ℕ ↦ Icc (-n : α) n := by
  refine fun m n hmn ↦ by apply Icc_subset_Icc <;> simpa using Nat.mono_cast hmn

variable [DecidableEq α]

def box : ℕ → Finset α := disjointed fun n ↦ Icc (-n : α) n

omit [IsOrderedRing α] in
