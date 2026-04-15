/-
Extracted from Data/Set/Subset.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sets in subtypes

This file is about sets in `Set A` when `A` is a set.

It defines notation `↓∩` for sets in a type pulled down to sets in a subtype, as an inverse
operation to the coercion that lifts sets in a subtype up to sets in the ambient type.

This module also provides lemmas for `↓∩` and this coercion.

## Notation

Let `α` be a `Type`, `A B : Set α` two sets in `α`, and `C : Set A` a set in the subtype `↑A`.

- `A ↓∩ B` denotes `(Subtype.val ⁻¹' B : Set A)` (that is, `{x : ↑A | ↑x ∈ B}`).
- `↑C` denotes `Subtype.val '' C` (that is, `{x : α | ∃ y ∈ C, ↑y = x}`).

This notation, (together with the `↑` notation for `Set.CoeHead`)
is defined in `Mathlib/Data/Set/Notation.lean` and is scoped to the `Set.Notation` namespace.
To enable it, use `open Set.Notation`.


## Naming conventions

Theorem names refer to `↓∩` as `preimage_val`.

## Tags

subsets
-/

open Set

variable {ι : Sort*} {α : Type*} {A B C : Set α} {D E : Set A}

variable {S : Set (Set α)} {T : Set (Set A)} {s : ι → Set α} {t : ι → Set A}

namespace Set

open Notation

lemma preimage_val_eq_univ_of_subset (h : A ⊆ B) : A ↓∩ B = univ := by
  rw [eq_univ_iff_forall, Subtype.forall]
  exact h

lemma preimage_val_sUnion : A ↓∩ (⋃₀ S) = ⋃₀ { (A ↓∩ B) | B ∈ S } := by
  rw [← Set.image, sUnion_image]
  simp_rw [sUnion_eq_biUnion, preimage_iUnion]
