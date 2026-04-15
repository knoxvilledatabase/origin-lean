/-
Extracted from Data/List/Intervals.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Intervals in ℕ

This file defines intervals of naturals. `List.Ico m n` is the list of integers greater than `m`
and strictly less than `n`.

## TODO
- Define `Ioo` and `Icc`, state basic lemmas about them.
- Also do the versions for integers?
- One could generalise even further, defining 'locally finite partial orders', for which
  `Set.Ico a b` is `[Finite]`, and 'locally finite total orders', for which there is a list model.
- Once the above is done, get rid of `Int.range` (and maybe `List.range'`?).
-/

open Nat

namespace List

def Ico (n m : ℕ) : List ℕ :=
  range' n (m - n)

namespace Ico

theorem zero_bot (n : ℕ) : Ico 0 n = range n := by rw [Ico, Nat.sub_zero, range_eq_range']
