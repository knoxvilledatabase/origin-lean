/-
Extracted from Order/Bounds/Lattice.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Unions and intersections of bounds

Some results about upper and lower bounds over collections of sets.

## Implementation notes

In a separate file as we need to import `Mathlib/Data/Set/Lattice.lean`.

-/

variable {α : Type*} [Preorder α] {ι : Sort*} {s : ι → Set α}

open Set

theorem gc_upperBounds_lowerBounds : GaloisConnection
    (OrderDual.toDual ∘ upperBounds : Set α → (Set α)ᵒᵈ)
    (lowerBounds ∘ OrderDual.ofDual : (Set α)ᵒᵈ → Set α) := by
  simpa [GaloisConnection, subset_def, mem_upperBounds, mem_lowerBounds]
    using fun S T ↦ forall₂_comm
