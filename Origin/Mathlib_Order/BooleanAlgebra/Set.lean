/-
Extracted from Order/BooleanAlgebra/Set.lean
Genuine: 10 of 16 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Boolean algebra of sets

This file proves that `Set α` is a Boolean algebra, and proves results about set difference and
complement.

## Notation

* `sᶜ` for the complement of `s`

## Tags

set, sets, subset, subsets, complement
-/

assert_not_exists RelIso

open Function

namespace Set

variable {α β : Type*} {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instBooleanAlgebra

lemma inter_diff_assoc (a b c : Set α) : (a ∩ b) \ c = a ∩ (b \ c) := inf_sdiff_assoc ..

lemma sdiff_inter_right_comm (s t u : Set α) : s \ t ∩ u = (s ∩ u) \ t := sdiff_inf_right_comm ..

lemma inter_sdiff_left_comm (s t u : Set α) : s ∩ (t \ u) = t ∩ (s \ u) := inf_sdiff_left_comm ..

theorem diff_union_diff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut

theorem diff_union_diff_cancel' (hi : s ∩ u ⊆ t) (hu : t ⊆ s ∪ u) : (s \ t) ∪ (t \ u) = s \ u :=
  sdiff_sup_sdiff_cancel' hi hu

theorem diff_diff_eq_sdiff_union (h : u ⊆ s) : s \ (t \ u) = s \ t ∪ u := sdiff_sdiff_eq_sdiff_sup h

theorem inter_diff_distrib_left (s t u : Set α) : s ∩ (t \ u) = (s ∩ t) \ (s ∩ u) :=
  inf_sdiff_distrib_left _ _ _

theorem inter_diff_distrib_right (s t u : Set α) : (s \ t) ∩ u = (s ∩ u) \ (t ∩ u) :=
  inf_sdiff_distrib_right _ _ _

theorem diff_inter_distrib_right (s t r : Set α) : (t ∩ r) \ s = (t \ s) ∩ (r \ s) :=
  inf_sdiff

/-! ### Lemmas about complement -/

theorem notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x ∈ s :=
  not_not
