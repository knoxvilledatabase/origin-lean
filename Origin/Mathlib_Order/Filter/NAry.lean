/-
Extracted from Order/Filter/NAry.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# N-ary maps of filter

This file defines the binary and ternary maps of filters. This is mostly useful to define pointwise
operations on filters.

## Main declarations

* `Filter.map₂`: Binary map of filters.

## Notes

This file is very similar to `Mathlib/Data/Set/NAry.lean`, `Mathlib/Data/Finset/NAry.lean` and
`Mathlib/Data/Option/NAry.lean`. Please keep them in sync.
-/

open Function Set

open Filter

namespace Filter

variable {α α' β β' γ γ' δ δ' ε ε' : Type*} {m : α → β → γ} {f f₁ f₂ : Filter α}
  {g g₁ g₂ : Filter β} {h : Filter γ} {s : Set α} {t : Set β} {u : Set γ}
  {a : α} {b : β}

def map₂ (m : α → β → γ) (f : Filter α) (g : Filter β) : Filter γ :=
  ((f ×ˢ g).map (uncurry m)).copy { s | ∃ u ∈ f, ∃ v ∈ g, image2 m u v ⊆ s } fun _ ↦ by
    simp only [mem_map, mem_prod_iff, image2_subset_iff, prod_subset_iff]; rfl
