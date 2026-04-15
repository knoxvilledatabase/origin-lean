/-
Extracted from Data/List/TakeDrop.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `Take` and `Drop` lemmas for lists

This file provides lemmas about `List.take` and `List.drop` and related functions.
-/

assert_not_exists GroupWithZero

assert_not_exists Lattice

assert_not_exists Prod.swap_eq_iff_eq_swap

assert_not_exists Ring

assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l₁ l₂ : List α}

/-! ### take, drop -/

theorem take_one_drop_eq_of_lt_length {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.get ⟨n, h⟩] := by
  rw [drop_eq_getElem_cons h, take, take]
  simp
