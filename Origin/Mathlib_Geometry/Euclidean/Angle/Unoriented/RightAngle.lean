/-
Extracted from Geometry/Euclidean/Angle/Unoriented/RightAngle.lean
Genuine: 32 of 50 | Dissolved: 18 | Infrastructure: 0
-/
import Origin.Core

/-!
# Right-angled triangles

This file proves basic geometric results about distances and angles in (possibly degenerate)
right-angled triangles in real inner product spaces and Euclidean affine spaces.

## Implementation notes

Results in this file are generally given in a form with only those non-degeneracy conditions
needed for the particular result, rather than requiring affine independence of the points of a
triangle unnecessarily.

## References

* https://en.wikipedia.org/wiki/Pythagorean_theorem

-/

noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 := by
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

theorem norm_add_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 := by
  rw [norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

theorem norm_sub_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

theorem angle_add_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖) := by
  rw [angle, inner_add_right, h, add_zero, real_inner_self_eq_norm_mul_norm]
  by_cases hx : ‖x‖ = 0; · simp [hx]
  rw [div_mul_eq_div_div, mul_self_div_self]

-- DISSOLVED: angle_add_eq_arcsin_of_inner_eq_zero

-- DISSOLVED: angle_add_eq_arctan_of_inner_eq_zero

-- DISSOLVED: angle_add_pos_of_inner_eq_zero

theorem angle_add_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x + y) ≤ π / 2 := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h, Real.arccos_le_pi_div_two]
  exact div_nonneg (norm_nonneg _) (norm_nonneg _)

-- DISSOLVED: angle_add_lt_pi_div_two_of_inner_eq_zero

theorem cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x + y)) = ‖x‖ / ‖x + y‖ := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h,
    Real.cos_arccos (le_trans (by simp) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
      (div_le_one_of_le₀ _ (norm_nonneg _))]
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _),
    norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  exact le_add_of_nonneg_right (mul_self_nonneg _)

-- DISSOLVED: sin_angle_add_of_inner_eq_zero

theorem tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.tan (angle x (x + y)) = ‖y‖ / ‖x‖ := by
  by_cases h0 : x = 0; · simp [h0]
  rw [angle_add_eq_arctan_of_inner_eq_zero h h0, Real.tan_arctan]

theorem cos_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x + y)) * ‖x + y‖ = ‖x‖ := by
  rw [cos_angle_add_of_inner_eq_zero h]
  by_cases hxy : ‖x + y‖ = 0
  · have h' := norm_add_sq_eq_norm_sq_add_norm_sq_real h
    rw [hxy, zero_mul, eq_comm,
      add_eq_zero_iff_of_nonneg (mul_self_nonneg ‖x‖) (mul_self_nonneg ‖y‖), mul_self_eq_zero] at h'
    simp [h'.1]
  · exact div_mul_cancel₀ _ hxy

theorem sin_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.sin (angle x (x + y)) * ‖x + y‖ = ‖y‖ := by
  by_cases h0 : x = 0 ∧ y = 0; · simp [h0]
  rw [not_and_or] at h0
  rw [sin_angle_add_of_inner_eq_zero h h0, div_mul_cancel₀]
  rw [← mul_self_ne_zero, norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  refine (ne_of_lt ?_).symm
  rcases h0 with (h0 | h0)
  · exact Left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)
  · exact Left.add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.2 (norm_ne_zero_iff.2 h0))

-- DISSOLVED: tan_angle_add_mul_norm_of_inner_eq_zero

-- DISSOLVED: norm_div_cos_angle_add_of_inner_eq_zero

-- DISSOLVED: norm_div_sin_angle_add_of_inner_eq_zero

-- DISSOLVED: norm_div_tan_angle_add_of_inner_eq_zero

theorem angle_sub_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x - y) = Real.arccos (‖x‖ / ‖x - y‖) := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, angle_add_eq_arccos_of_inner_eq_zero h]

-- DISSOLVED: angle_sub_eq_arcsin_of_inner_eq_zero

-- DISSOLVED: angle_sub_eq_arctan_of_inner_eq_zero

-- DISSOLVED: angle_sub_pos_of_inner_eq_zero

theorem angle_sub_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x - y) ≤ π / 2 := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg]
  exact angle_add_le_pi_div_two_of_inner_eq_zero h

-- DISSOLVED: angle_sub_lt_pi_div_two_of_inner_eq_zero

theorem cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x - y)) = ‖x‖ / ‖x - y‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, cos_angle_add_of_inner_eq_zero h]

-- DISSOLVED: sin_angle_sub_of_inner_eq_zero

theorem tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.tan (angle x (x - y)) = ‖y‖ / ‖x‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, tan_angle_add_of_inner_eq_zero h, norm_neg]

theorem cos_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x - y)) * ‖x - y‖ = ‖x‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, cos_angle_add_mul_norm_of_inner_eq_zero h]

theorem sin_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.sin (angle x (x - y)) * ‖x - y‖ = ‖y‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, sin_angle_add_mul_norm_of_inner_eq_zero h, norm_neg]

-- DISSOLVED: tan_angle_sub_mul_norm_of_inner_eq_zero

-- DISSOLVED: norm_div_cos_angle_sub_of_inner_eq_zero

-- DISSOLVED: norm_div_sin_angle_sub_of_inner_eq_zero

-- DISSOLVED: norm_div_tan_angle_sub_of_inner_eq_zero

end InnerProductGeometry

namespace EuclideanGeometry

open InnerProductGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

theorem dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔
      ∠ p₁ p₂ p₃ = π / 2 := by
  erw [dist_comm p₃ p₂, dist_eq_norm_vsub V p₁ p₃, dist_eq_norm_vsub V p₁ p₂,
    dist_eq_norm_vsub V p₂ p₃, ← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
    vsub_sub_vsub_cancel_right p₁, ← neg_vsub_eq_vsub_rev p₂ p₃, norm_neg]

theorem angle_eq_arccos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    ∠ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃) := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, angle_add_eq_arccos_of_inner_eq_zero h]

theorem angle_eq_arcsin_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) : ∠ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁ p₃) := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V, @ne_comm _ p₃, ← @vsub_ne_zero V _ _ _ p₂, or_comm] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, angle_add_eq_arcsin_of_inner_eq_zero h h0]

theorem angle_eq_arctan_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₃ ≠ p₂) : ∠ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂) := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [ne_comm, ← @vsub_ne_zero V] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, angle_add_eq_arctan_of_inner_eq_zero h h0]

theorem angle_pos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : 0 < ∠ p₂ p₃ p₁ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V, eq_comm, ← @vsub_eq_zero_iff_eq V, or_comm] at h0
  rw [angle, ← vsub_add_vsub_cancel p₁ p₂ p₃, add_comm]
  exact angle_add_pos_of_inner_eq_zero h h0

theorem angle_le_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    ∠ p₂ p₃ p₁ ≤ π / 2 := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, ← vsub_add_vsub_cancel p₁ p₂ p₃, add_comm]
  exact angle_add_le_pi_div_two_of_inner_eq_zero h

theorem angle_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₃ ≠ p₂) : ∠ p₂ p₃ p₁ < π / 2 := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [ne_comm, ← @vsub_ne_zero V] at h0
  rw [angle, ← vsub_add_vsub_cancel p₁ p₂ p₃, add_comm]
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0

theorem cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.cos (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, cos_angle_add_of_inner_eq_zero h]

theorem sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) : Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V, @ne_comm _ p₃, ← @vsub_ne_zero V _ _ _ p₂, or_comm] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, sin_angle_add_of_inner_eq_zero h h0]

theorem tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.tan (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, tan_angle_add_of_inner_eq_zero h]

theorem cos_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.cos (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, cos_angle_add_mul_norm_of_inner_eq_zero h]

theorem sin_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.sin (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, sin_angle_add_mul_norm_of_inner_eq_zero h]

theorem tan_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ = p₂ ∨ p₃ ≠ p₂) : Real.tan (∠ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [ne_comm, ← @vsub_ne_zero V, ← @vsub_eq_zero_iff_eq V, or_comm] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, tan_angle_add_mul_norm_of_inner_eq_zero h h0]

theorem dist_div_cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ = p₂ ∨ p₃ ≠ p₂) : dist p₃ p₂ / Real.cos (∠ p₂ p₃ p₁) = dist p₁ p₃ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [ne_comm, ← @vsub_ne_zero V, ← @vsub_eq_zero_iff_eq V, or_comm] at h0
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, norm_div_cos_angle_add_of_inner_eq_zero h h0]

theorem dist_div_sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₃ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [eq_comm, ← @vsub_ne_zero V, ← @vsub_eq_zero_iff_eq V, or_comm] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, norm_div_sin_angle_add_of_inner_eq_zero h h0]

theorem dist_div_tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.tan (∠ p₂ p₃ p₁) = dist p₃ p₂ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [eq_comm, ← @vsub_ne_zero V, ← @vsub_eq_zero_iff_eq V, or_comm] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, norm_div_tan_angle_add_of_inner_eq_zero h h0]

end EuclideanGeometry
