/-
Extracted from Data/Finset/Lattice/Lemmas.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about the lattice structure of finite sets

This file contains many results on the lattice structure of `Finset α`, in particular the
interaction between union, intersection, empty set and inserting elements.

## Tags

finite sets, finset

-/

assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

/-! ### Lattice structure -/

section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a b : α}

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

/-! #### union -/
