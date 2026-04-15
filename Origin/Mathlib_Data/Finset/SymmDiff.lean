/-
Extracted from Data/Finset/SymmDiff.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Symmetric difference of finite sets

This file concerns the symmetric difference operator `s Δ t` on finite sets.

## Tags

finite sets, finset

-/

assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

/-! ### Symmetric difference -/

section SymmDiff

open scoped symmDiff

variable [DecidableEq α] {s t : Finset α} {a b : α}

theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s := by
  simp_rw [symmDiff, sup_eq_union, mem_union, mem_sdiff]
