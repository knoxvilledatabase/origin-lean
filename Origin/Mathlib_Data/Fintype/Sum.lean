/-
Extracted from Data/Fintype/Sum.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
## Instances

We provide the `Fintype` instance for the sum of two fintypes.
-/

universe u v

variable {α β : Type*}

open Finset

-- INSTANCE (free from Core): (α

namespace Finset

variable {α β : Type*} {u : Finset (α ⊕ β)} {s : Finset α} {t : Finset β}

section left

variable [Fintype α] {u : Finset (α ⊕ β)}

lemma toLeft_eq_univ : u.toLeft = univ ↔ univ.map .inl ⊆ u := by
  simp [map_inl_subset_iff_subset_toLeft]

lemma toRight_eq_empty : u.toRight = ∅ ↔ u ⊆ univ.map .inl := by simp [subset_map_inl]

end left

section right

variable [Fintype β] {u : Finset (α ⊕ β)}

lemma toRight_eq_univ : u.toRight = univ ↔ univ.map .inr ⊆ u := by
  simp [map_inr_subset_iff_subset_toRight]

lemma toLeft_eq_empty : u.toLeft = ∅ ↔ u ⊆ univ.map .inr := by simp [subset_map_inr]

end right

variable [Fintype α] [Fintype β]
