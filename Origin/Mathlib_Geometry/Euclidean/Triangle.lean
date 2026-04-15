/-
Extracted from Geometry/Euclidean/Triangle.lean
Genuine: 24 of 31 | Dissolved: 7 | Infrastructure: 0
-/
import Origin.Core

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
* https://en.wikipedia.org/wiki/Law_of_sines

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

theorem sin_angle_mul_norm_eq_sin_angle_mul_norm (x y : V) :
    Real.sin (angle x y) * ‖x‖ = Real.sin (angle y (x - y)) * ‖x - y‖ := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  obtain rfl | hx := eq_or_ne x 0
  · simp [angle_neg_right, angle_self hy]
  obtain rfl | hxy := eq_or_ne x y
  · simp [angle_self hx]
  have h_sin (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
      Real.sin (angle x y) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) / (‖x‖ * ‖y‖) := by
    simp [field, mul_assoc, sin_angle_mul_norm_mul_norm]
  rw [h_sin x y hx hy, h_sin y (x - y) hy (sub_ne_zero_of_ne hxy)]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm x y]
  have hsub : x - y ≠ 0 := sub_ne_zero_of_ne hxy
  field_simp
  ring_nf

-- DISSOLVED: sin_angle_div_norm_eq_sin_angle_div_norm

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

-- DISSOLVED: cos_angle_eq_cos_angle_add_add_angle_add

-- DISSOLVED: sin_angle_eq_sin_angle_add_add_angle_add

-- DISSOLVED: angle_eq_angle_add_add_angle_add

-- DISSOLVED: angle_add_angle_sub_add_angle_sub_eq_pi

end InnerProductGeometry

namespace Orientation

open Module InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 2)]

variable (o : Orientation ℝ V (Fin 2))

-- DISSOLVED: norm_eq_of_two_zsmul_oangle_sub_eq

end Orientation

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

theorem dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ -
      2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃) := by
  rw [dist_eq_norm_vsub V p₁ p₃, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₃ p₂]
  unfold angle
  convert norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
    (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂ : V)
  · exact (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm
  · exact (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm

alias law_cos := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle

theorem sin_angle_mul_dist_eq_sin_angle_mul_dist (p₁ p₂ p₃ : P) :
    Real.sin (∠ p₁ p₂ p₃) * dist p₂ p₃ = Real.sin (∠ p₃ p₁ p₂) * dist p₃ p₁ := by
  simp only [dist_comm p₂ p₃, angle]
  rw [dist_eq_norm_vsub V p₃ p₂, dist_eq_norm_vsub V p₃ p₁, InnerProductGeometry.angle_comm,
    sin_angle_mul_norm_eq_sin_angle_mul_norm, vsub_sub_vsub_cancel_right, mul_eq_mul_right_iff]
  left
  rw [InnerProductGeometry.angle_comm, ← neg_vsub_eq_vsub_rev p₁ p₂, angle_neg_right,
    Real.sin_pi_sub]

alias law_sin := sin_angle_mul_dist_eq_sin_angle_mul_dist

set_option linter.flexible false in

set_option linter.unusedSimpArgs false in

theorem sin_angle_div_dist_eq_sin_angle_div_dist {p₁ p₂ p₃ : P} (h23 : p₂ ≠ p₃) (h31 : p₃ ≠ p₁) :
    Real.sin (∠ p₁ p₂ p₃) / dist p₃ p₁ = Real.sin (∠ p₃ p₁ p₂) / dist p₂ p₃ := by
  simp [field, dist_ne_zero.mpr h23, dist_ne_zero.mpr h31, mul_comm (dist ..)]
  exact law_sin _ _ _

theorem dist_eq_dist_mul_sin_angle_div_sin_angle {p₁ p₂ p₃ : P}
    (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    dist p₁ p₂ = dist p₃ p₁ * Real.sin (∠ p₂ p₃ p₁) / Real.sin (∠ p₁ p₂ p₃) := by
  have sin_gt_zero : 0 < Real.sin (∠ p₁ p₂ p₃) := sin_pos_of_not_collinear h
  field_simp
  rw [mul_comm, mul_comm (dist p₃ p₁), law_sin]

theorem angle_eq_angle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂ := by
  rw [dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃] at h
  unfold angle
  convert angle_sub_eq_angle_sub_rev_of_norm_eq h
  · exact (vsub_sub_vsub_cancel_left p₃ p₂ p₁).symm
  · exact (vsub_sub_vsub_cancel_left p₂ p₃ p₁).symm

theorem dist_eq_of_angle_eq_angle_of_angle_ne_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂)
    (hpi : ∠ p₂ p₁ p₃ ≠ π) : dist p₁ p₂ = dist p₁ p₃ := by
  unfold angle at h hpi
  rw [dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃]
  rw [← angle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hpi
  rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁, ← vsub_sub_vsub_cancel_left p₂ p₃ p₁] at h
  exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h hpi

-- DISSOLVED: dist_eq_of_two_zsmul_oangle_eq

theorem angle_add_angle_add_angle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π := by
  rw [add_assoc, add_comm, add_comm (∠ p₂ p₃ p₁), angle_comm p₂ p₃ p₁]
  unfold angle
  rw [← angle_neg_neg (p₁ -ᵥ p₃), ← angle_neg_neg (p₁ -ᵥ p₂), neg_vsub_eq_vsub_rev,
    neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, ←
    vsub_sub_vsub_cancel_right p₃ p₂ p₁, ← vsub_sub_vsub_cancel_right p₂ p₃ p₁]
  exact angle_add_angle_sub_add_angle_sub_eq_pi _ fun he => h (vsub_eq_zero_iff_eq.1 he)

theorem exterior_angle_eq_angle_add_angle {p₁ p₂ p₃ : P} (p : P) (h : Sbtw ℝ p p₁ p₂) :
    ∠ p₃ p₁ p = ∠ p₁ p₃ p₂ + ∠ p₃ p₂ p₁ := by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p₃ h.angle₁₂₃_eq_pi,
    angle_add_angle_add_angle_eq_pi p₃ h.right_ne.symm, angle_comm p₃ p₁ p₂]

theorem oangle_add_oangle_add_oangle_eq_pi [Module.Oriented ℝ V (Fin 2)]
    [Fact (Module.finrank ℝ V = 2)] {p₁ p₂ p₃ : P} (h21 : p₂ ≠ p₁) (h32 : p₃ ≠ p₂)
    (h13 : p₁ ≠ p₃) : ∡ p₁ p₂ p₃ + ∡ p₂ p₃ p₁ + ∡ p₃ p₁ p₂ = π := by
  simpa only [neg_vsub_eq_vsub_rev] using
    positiveOrientation.oangle_add_cyc3_neg_left (vsub_ne_zero.mpr h21) (vsub_ne_zero.mpr h32)
      (vsub_ne_zero.mpr h13)

lemma angle_add_of_ne_of_ne {a b c p : P} (hb : a ≠ b) (hc : a ≠ c) (hp : Wbtw ℝ b p c) :
    ∠ b a p + ∠ p a c = ∠ b a c := by
  by_cases pb : p = b; · simpa [pb] using angle_self_of_ne hb.symm
  by_cases pc : p = c; · simpa [pc] using angle_self_of_ne hc.symm
  have ea := angle_add_angle_add_angle_eq_pi c hb
  have eb := angle_add_angle_add_angle_eq_pi p hb
  have ec := angle_add_angle_add_angle_eq_pi p hc.symm
  replace hp : ∠ b p c = π := angle_eq_pi_iff_sbtw.mpr ⟨hp, pb, pc⟩
  have hp' : ∠ c p b = π := by rwa [angle_comm] at hp
  rw [angle_comm p b a, angle_eq_angle_of_angle_eq_pi a hp, angle_comm a b c] at eb
  rw [angle_eq_angle_of_angle_eq_pi a hp', angle_comm c p a] at ec
  have ep := angle_add_angle_eq_pi_of_angle_eq_pi a hp
  linarith only [ea, eb, ec, ep]

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
        field
      _ = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by
        rw [hm]
        field

theorem dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : ℝ) (h : ∠ a' b' c' = ∠ a b c)
    (hab : dist a' b' = r * dist a b) (hcb : dist c' b' = r * dist c b) :
    dist a' c' = r * dist a c := by
  have h' : dist a' c' ^ 2 = (r * dist a c) ^ 2 := calc
    dist a' c' ^ 2 =
        dist a' b' ^ 2 + dist c' b' ^ 2 - 2 * dist a' b' * dist c' b' * Real.cos (∠ a' b' c') := by
      simp [pow_two, law_cos a' b' c']
    _ = r ^ 2 * (dist a b ^ 2 + dist c b ^ 2 - 2 * dist a b * dist c b * Real.cos (∠ a b c)) := by
      rw [h, hab, hcb]; ring
    _ = (r * dist a c) ^ 2 := by simp [pow_two, ← law_cos a b c]; ring
  by_cases hab₁ : a = b
  · have hab'₁ : a' = b' := by
      rw [← dist_eq_zero, hab, dist_eq_zero.mpr hab₁, mul_zero r]
    rw [hab₁, hab'₁, dist_comm b' c', dist_comm b c, hcb]
  · have h1 : 0 ≤ r * dist a b := by rw [← hab]; exact dist_nonneg
    have h2 : 0 ≤ r := nonneg_of_mul_nonneg_left h1 (dist_pos.mpr hab₁)
    exact (sq_eq_sq₀ dist_nonneg (mul_nonneg h2 dist_nonneg)).mp h'

theorem dist_lt_of_angle_lt {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ∠ a c b < ∠ a b c → dist a b < dist a c := by
  have hsin := law_sin c b a
  rw [dist_comm b a, angle_comm c b a] at hsin
  have hac : dist a c > 0 := dist_pos.mpr (ne₁₃_of_not_collinear h)
  have hsinabc : Real.sin (∠ a b c) ≥ 0 := by
    apply Real.sin_nonneg_of_mem_Icc
    simp [angle_nonneg, angle_le_pi]
  intro h1
  by_cases! h2 : ∠ a b c ≤ π / 2
  · have h3 : Real.sin (∠ a c b) < Real.sin (∠ a b c) := by
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [angle_nonneg a c b]) h2 h1
    by_contra! w
    have h4 : Real.sin (∠ a c b) * dist a c < Real.sin (∠ a b c) * dist a b := by
      exact mul_lt_mul h3 w hac hsinabc
    linarith
  · by_contra! w
    have h3 : Real.sin (∠ a b c) ≤ Real.sin (∠ a c b) := by
      by_contra! w1
      have h4 : Real.sin (∠ a c b) * dist a c < Real.sin (∠ a b c) * dist a b := by
        exact mul_lt_mul w1 w hac hsinabc
      linarith
    rw [← Real.sin_pi_sub (∠ a b c)] at h3
    have h5 : π - ∠ a b c < π / 2 := by linarith
    have h6 : π - ∠ a b c ≤ ∠ a c b := by
      by_contra! w1
      have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [angle_nonneg a c b]) h5.le w1
      linarith
    have h7 := angle_add_angle_add_angle_eq_pi c (ne₁₂_of_not_collinear h).symm
    rw [angle_comm b c a] at h7
    have h8 : ∠ c a b > 0 := by
      rw [angle_comm]
      rw [show ({a, b, c} : Set P) = {b, a, c} by exact Set.insert_comm a b {c}] at h
      exact angle_pos_of_not_collinear h
    linarith

theorem angle_lt_iff_dist_lt {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ∠ a c b < ∠ a b c ↔ dist a b < dist a c := by
  constructor
  case mp =>
    exact dist_lt_of_angle_lt h
  case mpr =>
    intro h1
    by_contra! w
    rcases w.eq_or_lt with h2 | h3
    · have h4 : dist a b = dist a c := by
        apply dist_eq_of_angle_eq_angle_of_angle_ne_pi h2
        rw [show ({a, b, c} : Set P) = {b, a, c} by exact Set.insert_comm a b {c}] at h
        linarith [angle_lt_pi_of_not_collinear h]
      linarith
    · rw [show ({a, b, c} : Set P) = {a, c, b} by grind] at h
      have h5 := dist_lt_of_angle_lt h h3
      linarith

theorem angle_le_iff_dist_le {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ∠ a c b ≤ ∠ a b c ↔ dist a b ≤ dist a c := by
  rw [show ({a, b, c} : Set P) = {a, c, b} by grind] at h
  simpa using (angle_lt_iff_dist_lt h).not

lemma pi_div_three_le_angle_of_le_of_le {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ ≤ ∠ p₁ p₂ p₃)
    (h₃₁₂ : ∠ p₃ p₁ p₂ ≤ ∠ p₁ p₂ p₃) : π / 3 ≤ ∠ p₁ p₂ p₃ := by
  by_cases h : p₂ = p₁
  · rw [h, angle_self_left]
    linarith [Real.pi_pos]
  · linarith [angle_add_angle_add_angle_eq_pi p₃ h]

lemma pi_div_three_lt_angle_of_le_of_le_of_ne {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ ≤ ∠ p₁ p₂ p₃)
    (h₃₁₂ : ∠ p₃ p₁ p₂ ≤ ∠ p₁ p₂ p₃)
    (hne : ∠ p₁ p₂ p₃ ≠ ∠ p₂ p₃ p₁ ∨ ∠ p₁ p₂ p₃ ≠ ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ ≠ ∠ p₃ p₁ p₂) :
    π / 3 < ∠ p₁ p₂ p₃ := by
  by_cases h : p₂ = p₁
  · rw [h, angle_self_left]
    linarith [Real.pi_pos]
  · rcases hne with hne | hne | hne <;>
      rcases hne.lt_or_gt with hne | hne <;>
      linarith [angle_add_angle_add_angle_eq_pi p₃ h]

lemma angle_le_pi_div_three_of_le_of_le {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ ≤ ∠ p₂ p₃ p₁)
    (h₃₁₂ : ∠ p₁ p₂ p₃ ≤ ∠ p₃ p₁ p₂) (hnd : p₁ ≠ p₂ ∨ p₁ ≠ p₃ ∨ p₂ ≠ p₃) :
    ∠ p₁ p₂ p₃ ≤ π / 3 := by
  by_cases h : p₂ = p₁
  · subst h
    simp_all [angle_self_of_ne]
    linarith [Real.pi_pos]
  · linarith [angle_add_angle_add_angle_eq_pi p₃ h]

lemma angle_lt_pi_div_three_of_le_of_le_of_ne {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ ≤ ∠ p₂ p₃ p₁)
    (h₃₁₂ : ∠ p₁ p₂ p₃ ≤ ∠ p₃ p₁ p₂)
    (hne : ∠ p₁ p₂ p₃ ≠ ∠ p₂ p₃ p₁ ∨ ∠ p₁ p₂ p₃ ≠ ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ ≠ ∠ p₃ p₁ p₂) :
    ∠ p₁ p₂ p₃ < π / 3 := by
  by_cases h : p₂ = p₁
  · subst h
    by_cases h₂₃ : p₂ = p₃
    · subst h₂₃
      simp at hne
    · simp_all [angle_self_of_ne]
      linarith [Real.pi_pos]
  · rcases hne with hne | hne | hne <;>
      rcases hne.lt_or_gt with hne | hne <;>
      linarith [angle_add_angle_add_angle_eq_pi p₃ h]

end EuclideanGeometry
