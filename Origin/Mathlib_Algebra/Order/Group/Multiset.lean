/-
Extracted from Algebra/Order/Group/Multiset.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Multisets form an ordered monoid

This file contains the ordered monoid instance on multisets, and lemmas related to it.

See note [foundational algebra order theory].
-/

open List Nat

variable {α β : Type*}

namespace Multiset

/-! ### Additive monoid -/

-- INSTANCE (free from Core): instAddLeftMono

-- INSTANCE (free from Core): instAddLeftReflectLE

-- INSTANCE (free from Core): instAddCancelCommMonoid

lemma mem_of_mem_nsmul {a : α} {s : Multiset α} {n : ℕ} (h : a ∈ n • s) : a ∈ s := by
  induction n with
  | zero =>
    rw [zero_nsmul] at h
    exact absurd h (notMem_zero _)
  | succ n ih =>
    rw [succ_nsmul, mem_add] at h
    exact h.elim ih id
