/-
Extracted from Data/List/ToFinsupp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Lists as finsupp

## Main definitions

- `List.toFinsupp`: Interpret a list as a finitely supported function, where the indexing type is
  `ℕ`, and the values are either the elements of the list (accessing by indexing) or `0` outside of
  the list.

## Main theorems

- `List.toFinsupp_eq_sum_map_enum_single`: A `l : List M` over `M` an `AddMonoid`, when interpreted
  as a finitely supported function, is equal to the sum of `Finsupp.single` produced by mapping over
  `List.enum l`.

## Implementation details

The functions defined here rely on a decidability predicate that each element in the list
can be decidably determined to be not equal to zero or that one can decide one is out of the
bounds of a list. For concretely defined lists that are made up of elements of decidable terms,
this holds. More work will be needed to support lists over non-dec-eq types like `ℝ`, where the
elements are beyond the dec-eq terms of casted values from `ℕ, ℤ, ℚ`.
-/

namespace List

variable {M : Type*} [Zero M] (l : List M) [DecidablePred (getD l · 0 ≠ 0)] (n : ℕ)

def toFinsupp : ℕ →₀ M where
  toFun i := getD l i 0
  support := {i ∈ Finset.range l.length | getD l i 0 ≠ 0}
  mem_support_toFun n := by
    simp only [Ne, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    exact getD_eq_default _ _
