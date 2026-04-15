/-
Extracted from Geometry/Euclidean/Triangle.lean
Genuine: 11 | Conflates: 0 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Tactic.IntervalCases

/-!
# Triangles

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces. More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files. Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`LinearAlgebra.AffineSpace`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle

-/

noncomputable section

open scoped CharZero Real RealInnerProductSpace

namespace InnerProductGeometry

/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (x y : V) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) := by
  rw [show 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) = 2 * (Real.cos (angle x y) * (‖x‖ * ‖y‖)) by ring,
    cos_angle_mul_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, ←
    real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, real_inner_sub_sub_self,
    sub_add_eq_add_sub]

theorem angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
    angle x (x - y) = angle y (y - x) := by
  refine Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ?_
  rw [cos_angle, cos_angle, h, ← neg_sub, norm_neg, neg_sub, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm, h, real_inner_comm x y]

theorem norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V}
    (h : angle x (x - y) = angle y (y - x)) (hpi : angle x y ≠ π) : ‖x‖ = ‖y‖ := by
  replace h := Real.arccos_injOn (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x (x - y)))
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one y (y - x))) h
  by_cases hxy : x = y
  · rw [hxy]
  · rw [← norm_neg (y - x), neg_sub, mul_comm, mul_comm ‖y‖, div_eq_mul_inv, div_eq_mul_inv,
      mul_inv_rev, mul_inv_rev, ← mul_assoc, ← mul_assoc] at h
    replace h :=
      mul_right_cancel₀ (inv_ne_zero fun hz => hxy (eq_of_sub_eq_zero (norm_eq_zero.1 hz))) h
    rw [inner_sub_right, inner_sub_right, real_inner_comm x y, real_inner_self_eq_norm_mul_norm,
      real_inner_self_eq_norm_mul_norm, mul_sub_right_distrib, mul_sub_right_distrib,
      mul_self_mul_inv, mul_self_mul_inv, sub_eq_sub_iff_sub_eq_sub, ← mul_sub_left_distrib] at h
    by_cases hx0 : x = 0
    · rw [hx0, norm_zero, inner_zero_left, zero_mul, zero_sub, neg_eq_zero] at h
      rw [hx0, norm_zero, h]
    · by_cases hy0 : y = 0
      · rw [hy0, norm_zero, inner_zero_right, zero_mul, sub_zero] at h
        rw [hy0, norm_zero, h]
      · rw [inv_sub_inv (fun hz => hx0 (norm_eq_zero.1 hz)) fun hz => hy0 (norm_eq_zero.1 hz), ←
          neg_sub, ← mul_div_assoc, mul_comm, mul_div_assoc, ← mul_neg_one] at h
        symm
        by_contra hyx
        replace h := (mul_left_cancel₀ (sub_ne_zero_of_ne hyx) h).symm
        rw [real_inner_div_norm_mul_norm_eq_neg_one_iff, ← angle_eq_pi_iff] at h
        exact hpi h

-- DISSOLVED: cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle

-- DISSOLVED: sin_angle_sub_add_angle_sub_rev_eq_sin_angle

-- DISSOLVED: cos_angle_add_angle_sub_add_angle_sub_eq_neg_one

-- DISSOLVED: sin_angle_add_angle_sub_add_angle_sub_eq_zero

-- DISSOLVED: angle_add_angle_sub_add_angle_sub_eq_pi

end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possibly degenerate) triangles in Euclidean affine spaces.
-/

open InnerProductGeometry

open scoped EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

theorem dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (p1 p2 p3 : P) :
    dist p1 p3 * dist p1 p3 = dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 -
      2 * dist p1 p2 * dist p3 p2 * Real.cos (∠ p1 p2 p3) := by
  rw [dist_eq_norm_vsub V p1 p3, dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p3 p2]
  unfold angle
  convert norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
    (p1 -ᵥ p2 : V) (p3 -ᵥ p2 : V)
  · exact (vsub_sub_vsub_cancel_right p1 p3 p2).symm
  · exact (vsub_sub_vsub_cancel_right p1 p3 p2).symm

alias law_cos := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle

theorem angle_eq_angle_of_dist_eq {p1 p2 p3 : P} (h : dist p1 p2 = dist p1 p3) :
    ∠ p1 p2 p3 = ∠ p1 p3 p2 := by
  rw [dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p1 p3] at h
  unfold angle
  convert angle_sub_eq_angle_sub_rev_of_norm_eq h
  · exact (vsub_sub_vsub_cancel_left p3 p2 p1).symm
  · exact (vsub_sub_vsub_cancel_left p2 p3 p1).symm

theorem dist_eq_of_angle_eq_angle_of_angle_ne_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = ∠ p1 p3 p2)
    (hpi : ∠ p2 p1 p3 ≠ π) : dist p1 p2 = dist p1 p3 := by
  unfold angle at h hpi
  rw [dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p1 p3]
  rw [← angle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hpi
  rw [← vsub_sub_vsub_cancel_left p3 p2 p1, ← vsub_sub_vsub_cancel_left p2 p3 p1] at h
  exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h hpi

theorem angle_add_angle_add_angle_eq_pi {p1 p2 p3 : P} (h2 : p2 ≠ p1) (h3 : p3 ≠ p1) :
    ∠ p1 p2 p3 + ∠ p2 p3 p1 + ∠ p3 p1 p2 = π := by
  rw [add_assoc, add_comm, add_comm (∠ p2 p3 p1), angle_comm p2 p3 p1]
  unfold angle
  rw [← angle_neg_neg (p1 -ᵥ p3), ← angle_neg_neg (p1 -ᵥ p2), neg_vsub_eq_vsub_rev,
    neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, ←
    vsub_sub_vsub_cancel_right p3 p2 p1, ← vsub_sub_vsub_cancel_right p2 p3 p1]
  exact angle_add_angle_sub_add_angle_sub_eq_pi (fun he => h3 (vsub_eq_zero_iff_eq.1 he)) fun he =>
    h2 (vsub_eq_zero_iff_eq.1 he)

theorem oangle_add_oangle_add_oangle_eq_pi [Module.Oriented ℝ V (Fin 2)]
    [Fact (Module.finrank ℝ V = 2)] {p1 p2 p3 : P} (h21 : p2 ≠ p1) (h32 : p3 ≠ p2)
    (h13 : p1 ≠ p3) : ∡ p1 p2 p3 + ∡ p2 p3 p1 + ∡ p3 p1 p2 = π := by
  simpa only [neg_vsub_eq_vsub_rev] using
    positiveOrientation.oangle_add_cyc3_neg_left (vsub_ne_zero.mpr h21) (vsub_ne_zero.mpr h32)
      (vsub_ne_zero.mpr h13)

theorem dist_sq_mul_dist_add_dist_sq_mul_dist (a b c p : P) (h : ∠ b p c = π) :
    dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p =
    dist b c * (dist a p ^ 2 + dist b p * dist c p) := by
  rw [pow_two, pow_two, law_cos a p b, law_cos a p c,
    eq_sub_of_add_eq (angle_add_angle_eq_pi_of_angle_eq_pi a h), Real.cos_pi_sub,
    dist_eq_add_dist_of_angle_eq_pi h]
  ring

theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (a b c : P) :
    dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by
  by_cases hbc : b = c
  · simp [hbc, midpoint_self, dist_self, two_mul]
  · let m := midpoint ℝ b c
    have : dist b c ≠ 0 := (dist_pos.mpr hbc).ne'
    have hm := dist_sq_mul_dist_add_dist_sq_mul_dist a b c m (angle_midpoint_eq_pi b c hbc)
    simp only [m, dist_left_midpoint, dist_right_midpoint, Real.norm_two] at hm
    calc
      dist a b ^ 2 + dist a c ^ 2 = 2 / dist b c * (dist a b ^ 2 *
        ((2 : ℝ)⁻¹ * dist b c) + dist a c ^ 2 * (2⁻¹ * dist b c)) := by
        -- TODO(https://github.com/leanprover-community/mathlib4/issues/15486): used to be `field_simp`, but was really slow
        -- replaced by `simp only ...` to speed up. Reinstate `field_simp` once it is faster.
        simp (disch := field_simp_discharge) only [inv_eq_one_div, div_mul_eq_mul_div, one_mul,
          mul_div_assoc', add_div', div_mul_cancel₀, div_div, eq_div_iff]
        ring
      _ = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by
        rw [hm]
        -- TODO(https://github.com/leanprover-community/mathlib4/issues/15486): used to be `field_simp`, but was really slow
        -- replaced by `simp only ...` to speed up. Reinstate `field_simp` once it is faster.
        simp (disch := field_simp_discharge) only [inv_eq_one_div, div_mul_eq_mul_div, one_mul,
          mul_div_assoc', div_div, add_div', div_pow, eq_div_iff, div_eq_iff]
        ring

theorem dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : ℝ) (h : ∠ a' b' c' = ∠ a b c)
    (hab : dist a' b' = r * dist a b) (hcb : dist c' b' = r * dist c b) :
    dist a' c' = r * dist a c := by
  have h' : dist a' c' ^ 2 = (r * dist a c) ^ 2 := calc
    dist a' c' ^ 2 =
        dist a' b' ^ 2 + dist c' b' ^ 2 - 2 * dist a' b' * dist c' b' * Real.cos (∠ a' b' c') := by
      simp [pow_two, law_cos a' b' c']
    _ = r ^ 2 * (dist a b ^ 2 + dist c b ^ 2 - 2 * dist a b * dist c b * Real.cos (∠ a b c)) := by
      rw [h, hab, hcb]; ring
    _ = (r * dist a c) ^ 2 := by simp [pow_two, ← law_cos a b c, mul_pow]; ring
  by_cases hab₁ : a = b
  · have hab'₁ : a' = b' := by
      rw [← dist_eq_zero, hab, dist_eq_zero.mpr hab₁, mul_zero r]
    rw [hab₁, hab'₁, dist_comm b' c', dist_comm b c, hcb]
  · have h1 : 0 ≤ r * dist a b := by rw [← hab]; exact dist_nonneg
    have h2 : 0 ≤ r := nonneg_of_mul_nonneg_left h1 (dist_pos.mpr hab₁)
    exact (sq_eq_sq₀ dist_nonneg (mul_nonneg h2 dist_nonneg)).mp h'

end EuclideanGeometry
