/-
Extracted from Data/Nat/Dist.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Distance function on ℕ

This file defines a simple distance function on naturals from truncated subtraction.
-/

namespace Nat

def dist (n m : ℕ) :=
  n - m + (m - n)

theorem dist_comm (n m : ℕ) : dist n m = dist m n := by simp [dist, add_comm]
