/-
Extracted from Data/Finset/Disjoint.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Disjoint finite sets

## Main declarations

* `Disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
  intersection is empty.
* `Finset.disjUnion`: the union of the finite sets `s` and `t`, given a proof `Disjoint s t`

## Tags

finite sets, finset

-/

assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

variable {ι α β γ : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

/-! ### disjoint -/

section Disjoint

variable {f : α → β} {s t u : Finset α} {a b : α}

theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  ⟨fun h a hs ht => notMem_empty a <|
    singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
    fun h _ hs ht _ ha => (h (hs ha) (ht ha)).elim⟩

alias ⟨_root_.Disjoint.notMem_of_mem_left_finset, _⟩ := disjoint_left

theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by
  rw [_root_.disjoint_comm, disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right_finset, _⟩ := disjoint_right

theorem disjoint_iff_ne : Disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b := by
  simp only [disjoint_left, imp_not_comm, forall_eq']
