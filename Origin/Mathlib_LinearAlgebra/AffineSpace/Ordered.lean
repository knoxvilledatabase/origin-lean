/-
Extracted from LinearAlgebra/AffineSpace/Ordered.lean
Genuine: 24 of 24 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordered modules as affine spaces

In this file we prove some theorems about `slope` and `lineMap` in the case when the module `E`
acting on the codomain `PE` of a function is an ordered module over its domain `k`. We also prove
inequalities that can be used to link convexity of a function on an interval to monotonicity of the
slope, see section docstring below for details.

## Implementation notes

We do not introduce the notion of ordered affine spaces (yet?). Instead, we prove various theorems
for an ordered module interpreted as an affine space.

## Tags

affine space, ordered module, slope
-/

open AffineMap

variable {k E PE : Type*}

/-!
### Monotonicity of `lineMap`

In this section we prove that `lineMap a b r` is monotone (strictly or not) in its arguments if
other arguments belong to specific domains.
-/

section OrderedRing

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

theorem lineMap_mono_left (ha : a ≤ a') (hr : r ≤ 1) : lineMap a b r ≤ lineMap a' b r := by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_nonneg.2 hr

theorem lineMap_strict_mono_left (ha : a < a') (hr : r < 1) : lineMap a b r < lineMap a' b r := by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_pos.2 hr

omit [IsOrderedRing k] in

theorem lineMap_mono_right (hb : b ≤ b') (hr : 0 ≤ r) : lineMap a b r ≤ lineMap a b' r := by
  simp only [lineMap_apply_module]
  gcongr

omit [IsOrderedRing k] in

theorem lineMap_strict_mono_right (hb : b < b') (hr : 0 < r) : lineMap a b r < lineMap a b' r := by
  simp only [lineMap_apply_module]; gcongr

theorem lineMap_mono_endpoints (ha : a ≤ a') (hb : b ≤ b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r ≤ lineMap a' b' r :=
  (lineMap_mono_left ha h₁).trans (lineMap_mono_right hb h₀)

theorem lineMap_strict_mono_endpoints (ha : a < a') (hb : b < b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r < lineMap a' b' r := by
  rcases h₀.eq_or_lt with (rfl | h₀); · simpa
  exact (lineMap_mono_left ha.le h₁).trans_lt (lineMap_strict_mono_right hb h₀)

variable [PosSMulReflectLT k E]

theorem lineMap_lt_lineMap_iff_of_lt (h : r < r') : lineMap a b r < lineMap a b r' ↔ a < b := by
  simp only [lineMap_apply_module]
  rw [← lt_sub_iff_add_lt, add_sub_assoc, ← sub_lt_iff_lt_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_lt_smul_iff_of_pos_left (sub_pos.2 h)]

theorem left_lt_lineMap_iff_lt (h : 0 < r) : a < lineMap a b r ↔ a < b :=
  Iff.trans (by rw [lineMap_apply_zero]) (lineMap_lt_lineMap_iff_of_lt h)

theorem lineMap_lt_left_iff_lt (h : 0 < r) : lineMap a b r < a ↔ b < a :=
  left_lt_lineMap_iff_lt (E := Eᵒᵈ) h

theorem lineMap_lt_right_iff_lt (h : r < 1) : lineMap a b r < b ↔ a < b :=
  Iff.trans (by rw [lineMap_apply_one]) (lineMap_lt_lineMap_iff_of_lt h)

theorem right_lt_lineMap_iff_lt (h : r < 1) : b < lineMap a b r ↔ b < a :=
  lineMap_lt_right_iff_lt (E := Eᵒᵈ) h

end OrderedRing

section LinearOrderedRing

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem lineMap_le_lineMap_iff_of_lt' (h : a < b) : lineMap a b r ≤ lineMap a b r' ↔ r ≤ r' := by
  simp only [lineMap_apply_module']
  rw [add_le_add_iff_right, smul_le_smul_iff_of_pos_right (sub_pos.mpr h)]

theorem left_le_lineMap_iff_nonneg (h : a < b) : a ≤ lineMap a b r ↔ 0 ≤ r := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_zero]

theorem lineMap_le_left_iff_nonpos (h : a < b) : lineMap a b r ≤ a ↔ r ≤ 0 := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_zero]

theorem right_le_lineMap_iff_one_le (h : a < b) : b ≤ lineMap a b r ↔ 1 ≤ r := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_one]

theorem lineMap_le_right_iff_le_one (h : a < b) : lineMap a b r ≤ b ↔ r ≤ 1 := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_one]

theorem lineMap_lt_lineMap_iff_of_lt' (h : a < b) : lineMap a b r < lineMap a b r' ↔ r < r' := by
  simp only [lineMap_apply_module']
  rw [add_lt_add_iff_right, smul_lt_smul_iff_of_pos_right (sub_pos.mpr h)]

theorem left_lt_lineMap_iff_pos (h : a < b) : a < lineMap a b r ↔ 0 < r := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_zero]

theorem lineMap_lt_left_iff_neg (h : a < b) : lineMap a b r < a ↔ r < 0 := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_zero]

theorem right_lt_lineMap_iff_one_lt (h : a < b) : b < lineMap a b r ↔ 1 < r := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_one]

theorem lineMap_lt_right_iff_lt_one (h : a < b) : lineMap a b r < b ↔ r < 1 := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_one]

theorem midpoint_le_midpoint [Invertible (2 : k)] (ha : a ≤ a') (hb : b ≤ b') :
    midpoint k a b ≤ midpoint k a' b' :=
  lineMap_mono_endpoints ha hb (invOf_nonneg.2 zero_le_two) <| invOf_le_one one_le_two

end LinearOrderedRing

section LinearOrderedField

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem lineMap_le_lineMap_iff_of_lt (h : r < r') : lineMap a b r ≤ lineMap a b r' ↔ a ≤ b := by
  simp only [lineMap_apply_module]
  rw [← le_sub_iff_add_le, add_sub_assoc, ← sub_le_iff_le_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_le_smul_iff_of_pos_left (sub_pos.2 h)]

theorem left_le_lineMap_iff_le (h : 0 < r) : a ≤ lineMap a b r ↔ a ≤ b :=
  Iff.trans (by rw [lineMap_apply_zero]) (lineMap_le_lineMap_iff_of_lt h)
