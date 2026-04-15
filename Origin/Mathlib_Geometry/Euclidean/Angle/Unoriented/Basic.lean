/-
Extracted from Geometry/Euclidean/Angle/Unoriented/Basic.lean
Genuine: 31 | Conflates: 0 | Dissolved: 12 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Angles between vectors

This file defines unoriented angles in real inner product spaces.

## Main definitions

* `InnerProductGeometry.angle` is the undirected angle between two vectors.

## TODO

Prove the triangle inequality for the angle.
-/

noncomputable section

open Real Set

open Real

open RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {x y : V}

def angle (x y : V) : ℝ :=
  Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))

-- DISSOLVED: continuousAt_angle

-- DISSOLVED: angle_smul_smul

@[simp]
theorem _root_.LinearIsometry.angle_map {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] (f : E →ₗᵢ[ℝ] F) (u v : E) :
    angle (f u) (f v) = angle u v := by
  rw [angle, angle, f.inner_map_map, f.norm_map, f.norm_map]

@[simp, norm_cast]
theorem _root_.Submodule.angle_coe {s : Submodule ℝ V} (x y : s) :
    angle (x : V) (y : V) = angle x y :=
  s.subtypeₗᵢ.angle_map x y

theorem cos_angle (x y : V) : Real.cos (angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) :=
  Real.cos_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

theorem angle_comm (x y : V) : angle x y = angle y x := by
  unfold angle
  rw [real_inner_comm, mul_comm]

@[simp]
theorem angle_neg_neg (x y : V) : angle (-x) (-y) = angle x y := by
  unfold angle
  rw [inner_neg_neg, norm_neg, norm_neg]

theorem angle_nonneg (x y : V) : 0 ≤ angle x y :=
  Real.arccos_nonneg _

theorem angle_le_pi (x y : V) : angle x y ≤ π :=
  Real.arccos_le_pi _

theorem angle_neg_right (x y : V) : angle x (-y) = π - angle x y := by
  unfold angle
  rw [← Real.arccos_neg, norm_neg, inner_neg_right, neg_div]

theorem angle_neg_left (x y : V) : angle (-x) y = π - angle x y := by
  rw [← angle_neg_neg, neg_neg, angle_neg_right]

proof_wanted angle_triangle (x y z : V) : angle x z ≤ angle x y + angle y z

@[simp]
theorem angle_zero_left (x : V) : angle 0 x = π / 2 := by
  unfold angle
  rw [inner_zero_left, zero_div, Real.arccos_zero]

@[simp]
theorem angle_zero_right (x : V) : angle x 0 = π / 2 := by
  unfold angle
  rw [inner_zero_right, zero_div, Real.arccos_zero]

-- DISSOLVED: angle_self

-- DISSOLVED: angle_self_neg_of_nonzero

-- DISSOLVED: angle_neg_self_of_nonzero

@[simp]
theorem angle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : angle x (r • y) = angle x y := by
  unfold angle
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr), ← mul_assoc,
    mul_comm _ r, mul_assoc, mul_div_mul_left _ _ (ne_of_gt hr)]

@[simp]
theorem angle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : angle (r • x) y = angle x y := by
  rw [angle_comm, angle_smul_right_of_pos y x hr, angle_comm]

@[simp]
theorem angle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
    angle x (r • y) = angle x (-y) := by
  rw [← neg_neg r, neg_smul, angle_neg_right, angle_smul_right_of_pos x y (neg_pos_of_neg hr),
    angle_neg_right]

@[simp]
theorem angle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) : angle (r • x) y = angle (-x) y := by
  rw [angle_comm, angle_smul_right_of_neg y x hr, angle_comm]

theorem cos_angle_mul_norm_mul_norm (x y : V) : Real.cos (angle x y) * (‖x‖ * ‖y‖) = ⟪x, y⟫ := by
  rw [cos_angle, div_mul_cancel_of_imp]
  simp +contextual [or_imp]

theorem sin_angle_mul_norm_mul_norm (x y : V) :
    Real.sin (angle x y) * (‖x‖ * ‖y‖) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) := by
  unfold angle
  rw [Real.sin_arccos, ← Real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)),
    ← Real.sqrt_mul' _ (mul_self_nonneg _), sq,
    Real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)),
    real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm]
  by_cases h : ‖x‖ * ‖y‖ = 0
  · rw [show ‖x‖ * ‖x‖ * (‖y‖ * ‖y‖) = ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) by ring, h, mul_zero,
      mul_zero, zero_sub]
    cases' eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy
    · rw [norm_eq_zero] at hx
      rw [hx, inner_zero_left, zero_mul, neg_zero]
    · rw [norm_eq_zero] at hy
      rw [hy, inner_zero_right, zero_mul, neg_zero]
  · -- takes 600ms; squeezing the "equivalent" simp call yields an invalid result
    field_simp [h]
    ring_nf

-- DISSOLVED: angle_eq_zero_iff

-- DISSOLVED: angle_eq_pi_iff

theorem angle_add_angle_eq_pi_of_angle_eq_pi {x y : V} (z : V) (h : angle x y = π) :
    angle x z + angle y z = π := by
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩
  rw [angle_smul_left_of_neg x z hr, angle_neg_left, add_sub_cancel]

theorem inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2 :=
  Iff.symm <| by simp +contextual [angle, or_imp]

theorem inner_eq_neg_mul_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) :
    ⟪x, y⟫ = -(‖x‖ * ‖y‖) := by
  simp [← cos_angle_mul_norm_mul_norm, h]

theorem inner_eq_mul_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ⟪x, y⟫ = ‖x‖ * ‖y‖ := by
  simp [← cos_angle_mul_norm_mul_norm, h]

-- DISSOLVED: inner_eq_neg_mul_norm_iff_angle_eq_pi

-- DISSOLVED: inner_eq_mul_norm_iff_angle_eq_zero

theorem norm_sub_eq_add_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) :
    ‖x - y‖ = ‖x‖ + ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg (x - y)) (add_nonneg (norm_nonneg x) (norm_nonneg y)),
    norm_sub_pow_two_real, inner_eq_neg_mul_norm_of_angle_eq_pi h]
  ring

theorem norm_add_eq_add_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) :
    ‖x + y‖ = ‖x‖ + ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg (x + y)) (add_nonneg (norm_nonneg x) (norm_nonneg y)),
    norm_add_pow_two_real, inner_eq_mul_norm_of_angle_eq_zero h]
  ring

theorem norm_sub_eq_abs_sub_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) :
    ‖x - y‖ = |‖x‖ - ‖y‖| := by
  rw [← sq_eq_sq₀ (norm_nonneg (x - y)) (abs_nonneg (‖x‖ - ‖y‖)), norm_sub_pow_two_real,
    inner_eq_mul_norm_of_angle_eq_zero h, sq_abs (‖x‖ - ‖y‖)]
  ring

-- DISSOLVED: norm_sub_eq_add_norm_iff_angle_eq_pi

-- DISSOLVED: norm_add_eq_add_norm_iff_angle_eq_zero

-- DISSOLVED: norm_sub_eq_abs_sub_norm_iff_angle_eq_zero

theorem norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (x y : V) :
    ‖x + y‖ = ‖x - y‖ ↔ angle x y = π / 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg (x + y)) (norm_nonneg (x - y)),
    ← inner_eq_zero_iff_angle_eq_pi_div_two x y, norm_add_pow_two_real, norm_sub_pow_two_real]
  constructor <;> intro h <;> linarith

theorem cos_eq_one_iff_angle_eq_zero : cos (angle x y) = 1 ↔ angle x y = 0 := by
  rw [← cos_zero]
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (left_mem_Icc.2 pi_pos.le)

theorem cos_eq_zero_iff_angle_eq_pi_div_two : cos (angle x y) = 0 ↔ angle x y = π / 2 := by
  rw [← cos_pi_div_two]
  apply injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩
  constructor <;> linarith [pi_pos]

theorem cos_eq_neg_one_iff_angle_eq_pi : cos (angle x y) = -1 ↔ angle x y = π := by
  rw [← cos_pi]
  exact injOn_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (right_mem_Icc.2 pi_pos.le)

theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi :
    sin (angle x y) = 0 ↔ angle x y = 0 ∨ angle x y = π := by
  rw [sin_eq_zero_iff_cos_eq, cos_eq_one_iff_angle_eq_zero, cos_eq_neg_one_iff_angle_eq_pi]

theorem sin_eq_one_iff_angle_eq_pi_div_two : sin (angle x y) = 1 ↔ angle x y = π / 2 := by
  refine ⟨fun h => ?_, fun h => by rw [h, sin_pi_div_two]⟩
  rw [← cos_eq_zero_iff_angle_eq_pi_div_two, ← abs_eq_zero, abs_cos_eq_sqrt_one_sub_sin_sq, h]
  simp

end InnerProductGeometry
