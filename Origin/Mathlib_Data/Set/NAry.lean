/-
Extracted from Data/Set/NAry.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# N-ary images of sets

This file defines `Set.image2`, the binary image of sets.
This is mostly useful to define pointwise operations and `Set.seq`.

## Notes

This file is very similar to `Mathlib/Data/Finset/NAry.lean`, `Mathlib/Order/Filter/NAry.lean`, and
`Mathlib/Data/Option/NAry.lean`. Please keep them in sync.
-/

open Function

namespace Set

variable {α α' β β' γ γ' δ δ' ε ε' ζ ζ' ν : Type*} {f f' : α → β → γ}

variable {s s' : Set α} {t t' : Set β} {u : Set γ} {v : Set δ} {a : α} {b : β}

theorem mem_image2_iff (hf : Injective2 f) : f a b ∈ image2 f s t ↔ a ∈ s ∧ b ∈ t :=
  ⟨by
    rintro ⟨a', ha', b', hb', h⟩
    rcases hf h with ⟨rfl, rfl⟩
    exact ⟨ha', hb'⟩, fun ⟨ha, hb⟩ => mem_image2_of_mem ha hb⟩
