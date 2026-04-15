/-
Extracted from Data/Nat/Set.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
### Recursion on the natural numbers and `Set.range`
-/

namespace Nat

section Set

open Set

theorem zero_union_range_succ : {0} ∪ range succ = univ := by
  ext n
  cases n <;> simp
