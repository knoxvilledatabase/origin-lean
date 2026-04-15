/-
Extracted from Logic/Encodable/Lattice.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lattice operations on encodable types

Lemmas about lattice and set operations on encodable types

## Implementation Notes

This is a separate file, to avoid unnecessary imports in basic files.

Previously some of these results were in the `MeasureTheory` folder.
-/

open Set

namespace Encodable

variable {α : Type*} {β : Type*} [Encodable β]

theorem iSup_decode₂ [CompleteLattice α] (f : β → α) :
    ⨆ (i : ℕ) (b ∈ decode₂ β i), f b = (⨆ b, f b) := by
  rw [iSup_comm]
  simp only [mem_decode₂, iSup_iSup_eq_right]

theorem iUnion_decode₂ (f : β → Set α) : ⋃ (i : ℕ) (b ∈ decode₂ β i), f b = ⋃ b, f b :=
  iSup_decode₂ f
