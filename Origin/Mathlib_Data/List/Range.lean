/-
Extracted from Data/List/Range.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Ranges of naturals as lists

This file shows basic results about `List.iota`, `List.range`, `List.range'`
and defines `List.finRange`.
`finRange n` is the list of elements of `Fin n`.
`iota n = [n, n - 1, ..., 1]` and `range n = [0, ..., n - 1]` are basic list constructions used for
tactics. `range' a b = [a, ..., a + b - 1]` is there to help prove properties about them.
Actual maths should use `List.Ico` instead.
-/

universe u

open Nat

namespace List

variable {α : Type u}

theorem isChain_range (r : ℕ → ℕ → Prop) (n : ℕ) :
    IsChain r (range n) ↔ ∀ m < n - 1, r m m.succ := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp only [range_succ, Nat.add_one_sub_one, Nat.lt_sub_iff_add_lt] at hn ⊢
    cases n with
    | zero => simp
    | succ n =>
      simp only [range_succ, Nat.add_lt_add_iff_right, succ_eq_add_one, append_assoc, cons_append,
        nil_append, isChain_append_cons_cons, IsChain.singleton, and_true] at hn ⊢
      rw [hn, forall_lt_succ_right]

theorem isChain_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) :
    IsChain r (range n.succ) ↔ ∀ m < n, r m m.succ := by
  rw [isChain_range, succ_eq_add_one, Nat.add_one_sub_one]

theorem isChain_cons_range_succ (r : ℕ → ℕ → Prop) (n a : ℕ) :
    IsChain r (a :: range n.succ) ↔ r a 0 ∧ ∀ m < n, r m m.succ := by
  rw [range_succ_eq_map, isChain_cons_cons, and_congr_right_iff,
    ← isChain_range_succ, range_succ_eq_map]
  exact fun _ => Iff.rfl

section Ranges

def ranges : List ℕ → List (List ℕ)
  | [] => nil
  | a::l => range a::(ranges l).map (map (a + ·))

theorem ranges_disjoint (l : List ℕ) :
    Pairwise Disjoint (ranges l) := by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l hl =>
    simp only [ranges, pairwise_cons]
    constructor
    · intro s hs
      obtain ⟨s', _, rfl⟩ := mem_map.mp hs
      intro u hu
      rw [mem_map]
      rw [mem_range] at hu
      lia
    · rw [pairwise_map]
      apply Pairwise.imp _ hl
      intro u v
      apply disjoint_map
      exact fun u v => Nat.add_left_cancel

theorem ranges_length (l : List ℕ) :
    l.ranges.map length = l := by
  induction l with
  | nil => simp only [ranges, map_nil]
  | cons a l hl => -- (a :: l)
    simp only [ranges, map_cons, length_range, map_map, cons.injEq, true_and]
    conv_rhs => rw [← hl]
    apply map_congr_left
    intro s _
    simp only [Function.comp_apply, length_map]

end Ranges

end List
