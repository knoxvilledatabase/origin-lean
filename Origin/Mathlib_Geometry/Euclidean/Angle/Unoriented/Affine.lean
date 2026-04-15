/-
Extracted from Geometry/Euclidean/Angle/Unoriented/Affine.lean
Genuine: 51 | Conflates: 0 | Dissolved: 4 | Infrastructure: 7
-/
import Origin.Core
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Angles between points

This file defines unoriented angles in Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.angle`, with notation `∠`, is the undirected angle determined by three
  points.

## TODO

Prove the triangle inequality for the angle.
-/

noncomputable section

open Real RealInnerProductSpace

namespace EuclideanGeometry

open InnerProductGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {p p₀ : P}

nonrec def angle (p1 p2 p3 : P) : ℝ :=
  angle (p1 -ᵥ p2 : V) (p3 -ᵥ p2)

theorem continuousAt_angle {x : P × P × P} (hx12 : x.1 ≠ x.2.1) (hx32 : x.2.2 ≠ x.2.1) :
    ContinuousAt (fun y : P × P × P => ∠ y.1 y.2.1 y.2.2) x := by
  let f : P × P × P → V × V := fun y => (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1)
  have hf1 : (f x).1 ≠ 0 := by simp [hx12]
  have hf2 : (f x).2 ≠ 0 := by simp [hx32]
  exact (InnerProductGeometry.continuousAt_angle hf1 hf2).comp
    ((continuous_fst.vsub continuous_snd.fst).prod_mk
      (continuous_snd.snd.vsub continuous_snd.fst)).continuousAt

@[simp]
theorem _root_.AffineIsometry.angle_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂]
    [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    (f : P →ᵃⁱ[ℝ] P₂) (p₁ p₂ p₃ : P) : ∠ (f p₁) (f p₂) (f p₃) = ∠ p₁ p₂ p₃ := by
  simp_rw [angle, ← AffineIsometry.map_vsub, LinearIsometry.angle_map]

@[simp, norm_cast]
theorem _root_.AffineSubspace.angle_coe {s : AffineSubspace ℝ P} (p₁ p₂ p₃ : s) :
    haveI : Nonempty s := ⟨p₁⟩
    ∠ (p₁ : P) (p₂ : P) (p₃ : P) = ∠ p₁ p₂ p₃ :=
  haveI : Nonempty s := ⟨p₁⟩
  s.subtypeₐᵢ.angle_map p₁ p₂ p₃

@[simp]
theorem angle_const_vadd (v : V) (p₁ p₂ p₃ : P) : ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVAdd ℝ P v).toAffineIsometry.angle_map _ _ _

@[simp]
theorem angle_vadd_const (v₁ v₂ v₃ : V) (p : P) : ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) = ∠ v₁ v₂ v₃ :=
  (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.angle_map _ _ _

@[simp]
theorem angle_const_vsub (p p₁ p₂ p₃ : P) : ∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVSub ℝ p).toAffineIsometry.angle_map _ _ _

@[simp]
theorem angle_vsub_const (p₁ p₂ p₃ p : P) : ∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.vaddConst ℝ p).symm.toAffineIsometry.angle_map _ _ _

@[simp]
theorem angle_add_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ + v) (v₂ + v) (v₃ + v) = ∠ v₁ v₂ v₃ :=
  angle_vadd_const _ _ _ _

@[simp]
theorem angle_const_add (v : V) (v₁ v₂ v₃ : V) : ∠ (v + v₁) (v + v₂) (v + v₃) = ∠ v₁ v₂ v₃ :=
  angle_const_vadd _ _ _ _

@[simp]
theorem angle_sub_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ - v) (v₂ - v) (v₃ - v) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_vsub_const v₁ v₂ v₃ v

@[simp]
theorem angle_const_sub (v : V) (v₁ v₂ v₃ : V) : ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_const_vsub v v₁ v₂ v₃

@[simp]
theorem angle_neg (v₁ v₂ v₃ : V) : ∠ (-v₁) (-v₂) (-v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [zero_sub] using angle_const_sub 0 v₁ v₂ v₃

nonrec theorem angle_comm (p1 p2 p3 : P) : ∠ p1 p2 p3 = ∠ p3 p2 p1 :=
  angle_comm _ _

nonrec theorem angle_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ p1 p2 p3 :=
  angle_nonneg _ _

nonrec theorem angle_le_pi (p1 p2 p3 : P) : ∠ p1 p2 p3 ≤ π :=
  angle_le_pi _ _

@[simp] lemma angle_self_left (p₀ p : P) : ∠ p₀ p₀ p = π / 2 := by
  unfold angle
  rw [vsub_self]
  exact angle_zero_left _

@[simp] lemma angle_self_right (p₀ p : P) : ∠ p p₀ p₀ = π / 2 := by rw [angle_comm, angle_self_left]

theorem angle_self_of_ne (h : p ≠ p₀) : ∠ p p₀ p = 0 := angle_self <| vsub_ne_zero.2 h

theorem angle_eq_zero_of_angle_eq_pi_left {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : ∠ p2 p1 p3 = 0 := by
  unfold angle at h
  rw [angle_eq_pi_iff] at h
  rcases h with ⟨hp1p2, ⟨r, ⟨hr, hpr⟩⟩⟩
  unfold angle
  rw [angle_eq_zero_iff]
  rw [← neg_vsub_eq_vsub_rev, neg_ne_zero] at hp1p2
  use hp1p2, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one
  rw [add_smul, ← neg_vsub_eq_vsub_rev p1 p2, smul_neg]
  simp [← hpr]

theorem angle_eq_zero_of_angle_eq_pi_right {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
    ∠ p2 p3 p1 = 0 := by
  rw [angle_comm] at h
  exact angle_eq_zero_of_angle_eq_pi_left h

theorem angle_eq_angle_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
    ∠ p1 p2 p3 = ∠ p1 p2 p4 := by
  unfold angle at *
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, hpr⟩⟩⟩
  rw [eq_comm]
  convert angle_smul_right_of_pos (p1 -ᵥ p2) (p3 -ᵥ p2) (add_pos (neg_pos_of_neg hr) zero_lt_one)
  rw [add_smul, ← neg_vsub_eq_vsub_rev p2 p3, smul_neg, neg_smul, ← hpr]
  simp

nonrec theorem angle_add_angle_eq_pi_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
    ∠ p1 p3 p2 + ∠ p1 p3 p4 = π := by
  unfold angle at h
  rw [angle_comm p1 p3 p2, angle_comm p1 p3 p4]
  unfold angle
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h

theorem angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi {p1 p2 p3 p4 p5 : P} (hapc : ∠ p1 p5 p3 = π)
    (hbpd : ∠ p2 p5 p4 = π) : ∠ p1 p5 p2 = ∠ p3 p5 p4 := by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p1 hbpd, angle_comm p4 p5 p1,
    angle_add_angle_eq_pi_of_angle_eq_pi p4 hapc, angle_comm p4 p5 p3]

-- DISSOLVED: left_dist_ne_zero_of_angle_eq_pi

-- DISSOLVED: right_dist_ne_zero_of_angle_eq_pi

theorem dist_eq_add_dist_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
    dist p1 p3 = dist p1 p2 + dist p3 p2 := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_add_norm_of_angle_eq_pi h

theorem dist_eq_add_dist_iff_angle_eq_pi {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
    dist p1 p3 = dist p1 p2 + dist p3 p2 ↔ ∠ p1 p2 p3 = π := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_add_norm_iff_angle_eq_pi (fun he => hp1p2 (vsub_eq_zero_iff_eq.1 he)) fun he =>
      hp3p2 (vsub_eq_zero_iff_eq.1 he)

theorem dist_eq_abs_sub_dist_of_angle_eq_zero {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = 0) :
    dist p1 p3 = |dist p1 p2 - dist p3 p2| := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h

theorem dist_eq_abs_sub_dist_iff_angle_eq_zero {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
    dist p1 p3 = |dist p1 p2 - dist p3 p2| ↔ ∠ p1 p2 p3 = 0 := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_abs_sub_norm_iff_angle_eq_zero (fun he => hp1p2 (vsub_eq_zero_iff_eq.1 he))
      fun he => hp3p2 (vsub_eq_zero_iff_eq.1 he)

theorem angle_midpoint_eq_pi (p1 p2 : P) (hp1p2 : p1 ≠ p2) : ∠ p1 (midpoint ℝ p1 p2) p2 = π := by
  simp only [angle, left_vsub_midpoint, invOf_eq_inv, right_vsub_midpoint, inv_pos, zero_lt_two,
    angle_smul_right_of_pos, angle_smul_left_of_pos]
  rw [← neg_vsub_eq_vsub_rev p1 p2]
  apply angle_self_neg_of_nonzero
  simpa only [ne_eq, vsub_eq_zero_iff_eq]

theorem angle_left_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
    ∠ p3 (midpoint ℝ p1 p2) p1 = π / 2 := by
  let m : P := midpoint ℝ p1 p2
  have h1 : p3 -ᵥ p1 = p3 -ᵥ m - (p1 -ᵥ m) := (vsub_sub_vsub_cancel_right p3 p1 m).symm
  have h2 : p3 -ᵥ p2 = p3 -ᵥ m + (p1 -ᵥ m) := by
    rw [left_vsub_midpoint, ← midpoint_vsub_right, vsub_add_vsub_cancel]
  rw [dist_eq_norm_vsub V p3 p1, dist_eq_norm_vsub V p3 p2, h1, h2] at h
  exact (norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (p3 -ᵥ m) (p1 -ᵥ m)).mp h.symm

theorem angle_right_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
    ∠ p3 (midpoint ℝ p1 p2) p2 = π / 2 := by
  rw [midpoint_comm p1 p2, angle_left_midpoint_eq_pi_div_two_of_dist_eq h.symm]

theorem _root_.Sbtw.angle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₂ p₃ = π := by
  rw [angle, angle_eq_pi_iff]
  rcases h with ⟨⟨r, ⟨hr0, hr1⟩, hp₂⟩, hp₂p₁, hp₂p₃⟩
  refine ⟨vsub_ne_zero.2 hp₂p₁.symm, -(1 - r) / r, ?_⟩
  have hr0' : r ≠ 0 := by
    rintro rfl
    rw [← hp₂] at hp₂p₁
    simp at hp₂p₁
  have hr1' : r ≠ 1 := by
    rintro rfl
    rw [← hp₂] at hp₂p₃
    simp at hp₂p₃
  replace hr0 := hr0.lt_of_ne hr0'.symm
  replace hr1 := hr1.lt_of_ne hr1'
  refine ⟨div_neg_of_neg_of_pos (Left.neg_neg_iff.2 (sub_pos.2 hr1)) hr0, ?_⟩
  rw [← hp₂, AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, vsub_self,
    zero_sub, smul_neg, smul_smul, div_mul_cancel₀ _ hr0', neg_smul, neg_neg, sub_eq_iff_eq_add, ←
    add_smul, sub_add_cancel, one_smul]

theorem _root_.Sbtw.angle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₂ p₁ = π := by
  rw [← h.angle₁₂₃_eq_pi, angle_comm]

theorem angle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw ℝ p₁ p₂ p₃ := by
  refine ⟨?_, fun h => h.angle₁₂₃_eq_pi⟩
  rw [angle, angle_eq_pi_iff]
  rintro ⟨hp₁p₂, r, hr, hp₃p₂⟩
  refine ⟨⟨1 / (1 - r), ⟨div_nonneg zero_le_one (sub_nonneg.2 (hr.le.trans zero_le_one)),
    (div_le_one (sub_pos.2 (hr.trans zero_lt_one))).2 ((le_sub_self_iff 1).2 hr.le)⟩, ?_⟩,
    (vsub_ne_zero.1 hp₁p₂).symm, ?_⟩
  · rw [← eq_vadd_iff_vsub_eq] at hp₃p₂
    rw [AffineMap.lineMap_apply, hp₃p₂, vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev p₂ p₁, smul_neg, ←
      neg_smul, smul_add, smul_smul, ← add_smul, eq_comm, eq_vadd_iff_vsub_eq]
    convert (one_smul ℝ (p₂ -ᵥ p₁)).symm
    field_simp [(sub_pos.2 (hr.trans zero_lt_one)).ne.symm]
    ring
  · rw [ne_comm, ← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
    exact ⟨hr.ne, hp₁p₂⟩

theorem _root_.Wbtw.angle₂₁₃_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
    ∠ p₂ p₁ p₃ = 0 := by
  rw [angle, angle_eq_zero_iff]
  rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
  have hr0' : r ≠ 0 := by
    rintro rfl
    simp at hp₂p₁
  replace hr0 := hr0.lt_of_ne hr0'.symm
  refine ⟨vsub_ne_zero.2 hp₂p₁, r⁻¹, inv_pos.2 hr0, ?_⟩
  rw [AffineMap.lineMap_apply, vadd_vsub_assoc, vsub_self, add_zero, smul_smul,
    inv_mul_cancel₀ hr0', one_smul]

theorem _root_.Sbtw.angle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₁ p₃ = 0 :=
  h.wbtw.angle₂₁₃_eq_zero_of_ne h.ne_left

theorem _root_.Wbtw.angle₃₁₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
    ∠ p₃ p₁ p₂ = 0 := by rw [← h.angle₂₁₃_eq_zero_of_ne hp₂p₁, angle_comm]

theorem _root_.Sbtw.angle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₁ p₂ = 0 :=
  h.wbtw.angle₃₁₂_eq_zero_of_ne h.ne_left

theorem _root_.Wbtw.angle₂₃₁_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    ∠ p₂ p₃ p₁ = 0 :=
  h.symm.angle₂₁₃_eq_zero_of_ne hp₂p₃

theorem _root_.Sbtw.angle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₃ p₁ = 0 :=
  h.wbtw.angle₂₃₁_eq_zero_of_ne h.ne_right

theorem _root_.Wbtw.angle₁₃₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    ∠ p₁ p₃ p₂ = 0 :=
  h.symm.angle₃₁₂_eq_zero_of_ne hp₂p₃

theorem _root_.Sbtw.angle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₃ p₂ = 0 :=
  h.wbtw.angle₁₃₂_eq_zero_of_ne h.ne_right

theorem angle_eq_zero_iff_ne_and_wbtw {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁ := by
  constructor
  · rw [angle, angle_eq_zero_iff]
    rintro ⟨hp₁p₂, r, hr0, hp₃p₂⟩
    rcases le_or_lt 1 r with (hr1 | hr1)
    · refine Or.inl ⟨vsub_ne_zero.1 hp₁p₂, r⁻¹, ⟨(inv_pos.2 hr0).le, inv_le_one_of_one_le₀ hr1⟩, ?_⟩
      rw [AffineMap.lineMap_apply, hp₃p₂, smul_smul, inv_mul_cancel₀ hr0.ne.symm, one_smul,
        vsub_vadd]
    · refine Or.inr ⟨?_, r, ⟨hr0.le, hr1.le⟩, ?_⟩
      · rw [← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
        exact ⟨hr0.ne.symm, hp₁p₂⟩
      · rw [AffineMap.lineMap_apply, ← hp₃p₂, vsub_vadd]
  · rintro (⟨hp₁p₂, h⟩ | ⟨hp₃p₂, h⟩)
    · exact h.angle₂₁₃_eq_zero_of_ne hp₁p₂
    · exact h.angle₃₁₂_eq_zero_of_ne hp₃p₂

theorem angle_eq_zero_iff_eq_and_ne_or_sbtw {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ = p₃ ∧ p₁ ≠ p₂ ∨ Sbtw ℝ p₂ p₁ p₃ ∨ Sbtw ℝ p₂ p₃ p₁ := by
  rw [angle_eq_zero_iff_ne_and_wbtw]
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₁p₃ : p₁ = p₃; · simp [hp₁p₃]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  simp [hp₁p₂, hp₁p₃, Ne.symm hp₁p₃, Sbtw, hp₃p₂]

theorem collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · replace h := h.wbtw_or_wbtw_or_wbtw
    by_cases h₁₂ : p₁ = p₂
    · exact Or.inl h₁₂
    by_cases h₃₂ : p₃ = p₂
    · exact Or.inr (Or.inl h₃₂)
    rw [or_iff_right h₁₂, or_iff_right h₃₂]
    rcases h with (h | h | h)
    · exact Or.inr (angle_eq_pi_iff_sbtw.2 ⟨h, Ne.symm h₁₂, Ne.symm h₃₂⟩)
    · exact Or.inl (h.angle₃₁₂_eq_zero_of_ne h₃₂)
    · exact Or.inl (h.angle₂₃₁_eq_zero_of_ne h₁₂)
  · rcases h with (rfl | rfl | h | h)
    · simpa using collinear_pair ℝ p₁ p₃
    · simpa using collinear_pair ℝ p₁ p₃
    · rw [angle_eq_zero_iff_ne_and_wbtw] at h
      rcases h with (⟨-, h⟩ | ⟨-, h⟩)
      · rw [Set.insert_comm]
        exact h.collinear
      · rw [Set.insert_comm, Set.pair_comm]
        exact h.collinear
    · rw [angle_eq_pi_iff_sbtw] at h
      exact h.wbtw.collinear

theorem collinear_of_angle_eq_zero {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 <| Or.inr <| Or.inr <| Or.inl h

theorem collinear_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 <| Or.inr <| Or.inr <| Or.inr h

-- DISSOLVED: angle_ne_zero_of_not_collinear

theorem angle_ne_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ ≠ π :=
  mt collinear_of_angle_eq_pi h

theorem angle_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    0 < ∠ p₁ p₂ p₃ :=
  (angle_nonneg _ _ _).lt_of_ne (angle_ne_zero_of_not_collinear h).symm

theorem angle_lt_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ < π :=
  (angle_le_pi _ _ _).lt_of_ne <| angle_ne_pi_of_not_collinear h

nonrec theorem cos_eq_one_iff_angle_eq_zero {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = 0 :=
  cos_eq_one_iff_angle_eq_zero

nonrec theorem cos_eq_zero_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  cos_eq_zero_iff_angle_eq_pi_div_two

nonrec theorem cos_eq_neg_one_iff_angle_eq_pi {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = -1 ↔ ∠ p₁ p₂ p₃ = π :=
  cos_eq_neg_one_iff_angle_eq_pi

nonrec theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Real.sin (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π :=
  sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi

nonrec theorem sin_eq_one_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
    Real.sin (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  sin_eq_one_iff_angle_eq_pi_div_two

theorem collinear_iff_eq_or_eq_or_sin_eq_zero {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ Real.sin (∠ p₁ p₂ p₃) = 0 := by
  rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi,
    collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]

theorem sin_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    0 < Real.sin (∠ p₁ p₂ p₃) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear h) (angle_lt_pi_of_not_collinear h)

-- DISSOLVED: sin_ne_zero_of_not_collinear

theorem collinear_of_sin_eq_zero {p₁ p₂ p₃ : P} (h : Real.sin (∠ p₁ p₂ p₃) = 0) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
  revert h
  contrapose
  exact sin_ne_zero_of_not_collinear

end EuclideanGeometry
