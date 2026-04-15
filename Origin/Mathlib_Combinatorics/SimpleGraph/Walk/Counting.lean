/-
Extracted from Combinatorics/SimpleGraph/Walk/Counting.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Counting walks of a given length

## Main definitions
- `walkLengthTwoEquivCommonNeighbors`: bijective correspondence between walks of length two
  from `u` to `v` and common neighbours of `u` and `v`. Note that `u` and `v` may be the same.
- `finsetWalkLength`: the `Finset` of length-`n` walks from `u` to `v`.
  This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and it
  can also be useful as a recursive description of this set when `V` is finite.

TODO: should this be extended further?
-/

assert_not_exists Field

open Finset Function

universe u v w

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

theorem set_walk_length_zero_eq_of_ne {u v : V} (h : u ≠ v) :
    {p : G.Walk u v | p.length = 0} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact fun h' => absurd (Walk.eq_of_length_eq_zero h') h

theorem set_walk_length_succ_eq (u v : V) (n : ℕ) :
    {p : G.Walk u v | p.length = n.succ} =
      ⋃ (w : V) (h : G.Adj u w), Walk.cons h '' {p' : G.Walk w v | p'.length = n} := by
  ext p
  cases p with
  | nil => simp [eq_comm]
  | cons huw pwv =>
    simp only [Nat.succ_eq_add_one, Set.mem_setOf_eq, Walk.length_cons, add_left_inj,
      Set.mem_iUnion, Set.mem_image]
    grind
