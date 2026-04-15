/-
Extracted from Algebra/Order/Module/Pointwise.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bounds on scalar multiplication of set

This file proves order properties of pointwise operations of sets.
-/

open scoped Pointwise

variable {α β : Type*}

section PosSMulMono

variable [SMul α β] [Preorder α] [Preorder β] [Zero α] [PosSMulMono α β] {a : α} {s : Set β}

lemma smul_lowerBounds_subset_lowerBounds_smul_of_nonneg (ha : 0 ≤ a) :
    a • lowerBounds s ⊆ lowerBounds (a • s) :=
  (monotone_smul_left_of_nonneg ha).image_lowerBounds_subset_lowerBounds_image

lemma smul_upperBounds_subset_upperBounds_smul_of_nonneg (ha : 0 ≤ a) :
    a • upperBounds s ⊆ upperBounds (a • s) :=
  (monotone_smul_left_of_nonneg ha).image_upperBounds_subset_upperBounds_image

lemma BddBelow.smul_of_nonneg (hs : BddBelow s) (ha : 0 ≤ a) : BddBelow (a • s) :=
  (monotone_smul_left_of_nonneg ha).map_bddBelow hs

lemma BddAbove.smul_of_nonneg (hs : BddAbove s) (ha : 0 ≤ a) : BddAbove (a • s) :=
  (monotone_smul_left_of_nonneg ha).map_bddAbove hs

end PosSMulMono

variable [Preorder α] [Preorder β] [GroupWithZero α] [Zero β] [MulActionWithZero α β]
  [PosSMulMono α β] [PosSMulReflectLE α β] {s : Set β} {a : α}
