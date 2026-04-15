/-
Extracted from Topology/Clopen.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Clopen sets

A clopen set is a set that is both closed and open.
-/

open Set Filter Topology TopologicalSpace

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Clopen

protected theorem IsClopen.isOpen (hs : IsClopen s) : IsOpen s := hs.2

protected theorem IsClopen.isClosed (hs : IsClopen s) : IsClosed s := hs.1

theorem isClopen_iff_frontier_eq_empty : IsClopen s ↔ frontier s = ∅ := by
  rw [IsClopen, ← closure_eq_iff_isClosed, ← interior_eq_iff_isOpen, frontier, diff_eq_empty]
  refine ⟨fun h => (h.1.trans h.2.symm).subset, fun h => ?_⟩
  exact ⟨(h.trans interior_subset).antisymm subset_closure,
    interior_subset.antisymm (subset_closure.trans h)⟩
