/-
Extracted from Data/Multiset/UnionInter.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Distributive lattice structure on multisets

This file defines an instance `DistribLattice (Multiset α)` using the union and intersection
operators:

* `s ∪ t`: The multiset for which the number of occurrences of each `a` is the max of the
  occurrences of `a` in `s` and `t`.
* `s ∩ t`: The multiset for which the number of occurrences of each `a` is the min of the
  occurrences of `a` in `s` and `t`.
-/

assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

section sub

variable [DecidableEq α] {s t u : Multiset α} {a : α}

/-! ### Union -/

def union (s t : Multiset α) : Multiset α := s - t + t

-- INSTANCE (free from Core): :

lemma le_union_left : s ≤ s ∪ t := Multiset.le_sub_add

lemma le_union_right : t ≤ s ∪ t := le_add_left _ _

lemma eq_union_left : t ≤ s → s ∪ t = s := Multiset.sub_add_cancel
