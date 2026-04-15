/-
Extracted from NumberTheory/NumberField/InfinitePlace/Basic.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Infinite places of a number field

This file defines the infinite places of a number field.

## Main Definitions and Results

* `NumberField.InfinitePlace`: the type of infinite places of a number field `K`.
* `NumberField.InfinitePlace.mk_eq_iff`: two complex embeddings define the same infinite place iff
  they are equal or complex conjugates.
* `NumberField.InfinitePlace.IsReal`: The predicate on infinite places saying
  that a place is real, i.e., defined by a real embedding.
* `NumberField.InfinitePlace.IsComplex`: The predicate on infinite places saying
  that a place is complex, i.e., defined by a complex embedding that is not real.
* `NumberField.InfinitePlace.mult`: the multiplicity of an infinite place, that is the number of
  distinct complex embeddings that define it. So it is equal to `1` if the place is real and `2`
  if the place is complex.
* `NumberField.InfinitePlace.prod_eq_abs_norm`: the infinite part of the product formula, that is
  for `x ∈ K`, we have `Π_w ‖x‖_w = |norm(x)|` where the product is over the infinite place `w` and
  `‖·‖_w` is the normalized absolute value for `w`.
* `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`: the degree of `K` is equal to the
  number of real places plus twice the number of complex places.
* `NumberField.InfinitePlace.denseRange_algebraMap_pi`: the image of `K` by the diagonal embedding
  into the product of its infinite completions is dense.

## Tags

number field, infinite places
-/

open scoped Finset Topology

namespace NumberField

open Fintype Module

variable (K : Type*) [Field K]

def InfinitePlace := { w : AbsoluteValue K ℝ // ∃ φ : K →+* ℂ, place φ = w }

-- INSTANCE (free from Core): [Nonempty

variable {K}

noncomputable def InfinitePlace.mk (φ : K →+* ℂ) : InfinitePlace K :=
  ⟨place φ, ⟨φ, rfl⟩⟩

def IsInfinitePlace (w : AbsoluteValue K ℝ) : Prop :=
  ∃ φ : K →+* ℂ, place φ = w

lemma InfinitePlace.isInfinitePlace (v : InfinitePlace K) : IsInfinitePlace v.val := by
  simp [IsInfinitePlace, v.prop]

lemma isInfinitePlace_iff (v : AbsoluteValue K ℝ) :
    IsInfinitePlace v ↔ ∃ w : InfinitePlace K, w.val = v :=
  ⟨fun H ↦ ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ ↦ hw ▸ w.isInfinitePlace⟩

namespace InfinitePlace

-- INSTANCE (free from Core): :
