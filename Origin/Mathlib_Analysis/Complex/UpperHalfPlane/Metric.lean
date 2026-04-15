/-
Extracted from Analysis/Complex/UpperHalfPlane/Metric.lean
Genuine: 12 of 14 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Metric on the upper half-plane

In this file we define a `MetricSpace` structure on the `UpperHalfPlane`. We use hyperbolic
(Poincaré) distance given by
`dist z w = 2 * arsinh (dist (z : ℂ) w / (2 * √(z.im * w.im)))` instead of the induced
Euclidean distance because the hyperbolic distance is invariant under holomorphic automorphisms of
the upper half-plane. However, we ensure that the projection to `TopologicalSpace` is
definitionally equal to the induced topological space structure.

We also prove that a metric ball/closed ball/sphere in Poincaré metric is a Euclidean ball/closed
ball/sphere with another center and radius.

-/

noncomputable section

open Filter Metric Real Set Topology

open scoped UpperHalfPlane ComplexConjugate NNReal Topology MatrixGroups

variable {z w : ℍ} {r : ℝ}

namespace UpperHalfPlane

-- INSTANCE (free from Core): :

theorem sinh_half_dist (z w : ℍ) :
    sinh (dist z w / 2) = dist (z : ℂ) w / (2 * √(z.im * w.im)) := by
  rw [dist_eq, mul_div_cancel_left₀ (arsinh _) two_ne_zero, sinh_arsinh]

theorem cosh_half_dist (z w : ℍ) :
    cosh (dist z w / 2) = dist (z : ℂ) (conj (w : ℂ)) / (2 * √(z.im * w.im)) := by
  rw [← sq_eq_sq₀, cosh_sq', sinh_half_dist, div_pow, div_pow, one_add_div, mul_pow, sq_sqrt]
  · congr 1
    simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_conj,
      Complex.conj_conj, Complex.mul_re, Complex.conj_re, Complex.conj_im, coe_im]
    ring
  all_goals positivity

theorem tanh_half_dist (z w : ℍ) :
    tanh (dist z w / 2) = dist (z : ℂ) w / dist (z : ℂ) (conj ↑w) := by
  rw [tanh_eq_sinh_div_cosh, sinh_half_dist, cosh_half_dist, div_div_div_comm, div_self, div_one]
  positivity

theorem exp_half_dist (z w : ℍ) :
    exp (dist z w / 2) = (dist (z : ℂ) w + dist (z : ℂ) (conj ↑w)) / (2 * √(z.im * w.im)) := by
  rw [← sinh_add_cosh, sinh_half_dist, cosh_half_dist, add_div]

theorem cosh_dist (z w : ℍ) : cosh (dist z w) = 1 + dist (z : ℂ) w ^ 2 / (2 * z.im * w.im) := by
  rw [dist_eq, cosh_two_mul, cosh_sq', add_assoc, ← two_mul, sinh_arsinh, div_pow, mul_pow,
    sq_sqrt, sq (2 : ℝ), mul_assoc, ← mul_div_assoc, mul_assoc, mul_div_mul_left] <;> positivity

theorem sinh_half_dist_add_dist (a b c : ℍ) : sinh ((dist a b + dist b c) / 2) =
    (dist (a : ℂ) b * dist (c : ℂ) (conj ↑b) + dist (b : ℂ) c * dist (a : ℂ) (conj ↑b)) /
      (2 * √(a.im * c.im) * dist (b : ℂ) (conj ↑b)) := by
  simp only [add_div _ _ (2 : ℝ), sinh_add, sinh_half_dist, cosh_half_dist, div_mul_div_comm]
  rw [← add_div, Complex.dist_self_conj, coe_im, abs_of_pos b.im_pos, mul_comm (dist (b : ℂ) _),
    dist_comm (b : ℂ), Complex.dist_conj_comm, mul_mul_mul_comm, mul_mul_mul_comm _ _ _ b.im]
  congr 2
  rw [sqrt_mul, sqrt_mul, sqrt_mul, mul_comm (√a.im), mul_mul_mul_comm, mul_self_sqrt,
      mul_comm] <;> exact (im_pos _).le

protected theorem dist_comm (z w : ℍ) : dist z w = dist w z := by
  simp only [dist_eq, dist_comm (z : ℂ), mul_comm]

theorem dist_le_iff_le_sinh :
    dist z w ≤ r ↔ dist (z : ℂ) w / (2 * √(z.im * w.im)) ≤ sinh (r / 2) := by
  rw [← div_le_div_iff_of_pos_right (zero_lt_two' ℝ), ← sinh_le_sinh, sinh_half_dist]

theorem dist_eq_iff_eq_sinh :
    dist z w = r ↔ dist (z : ℂ) w / (2 * √(z.im * w.im)) = sinh (r / 2) := by
  rw [← div_left_inj' (two_ne_zero' ℝ), ← sinh_inj, sinh_half_dist]

theorem dist_eq_iff_eq_sq_sinh (hr : 0 ≤ r) :
    dist z w = r ↔ dist (z : ℂ) w ^ 2 / (4 * z.im * w.im) = sinh (r / 2) ^ 2 := by
  rw [dist_eq_iff_eq_sinh, ← sq_eq_sq₀, div_pow, mul_pow, sq_sqrt, mul_assoc]
  · norm_num
  all_goals positivity

protected theorem dist_triangle (a b c : ℍ) : dist a c ≤ dist a b + dist b c := by
  rw [dist_le_iff_le_sinh, sinh_half_dist_add_dist, div_mul_eq_div_div _ _ (dist _ _), le_div_iff₀,
    div_mul_eq_mul_div]
  · gcongr
    exact EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist (a : ℂ) b c (conj (b : ℂ))
  · rw [dist_comm, dist_pos, Ne, Complex.conj_eq_iff_im]
    exact b.im_ne_zero

theorem dist_le_dist_coe_div_sqrt (z w : ℍ) : dist z w ≤ dist (z : ℂ) w / √(z.im * w.im) := by
  rw [dist_le_iff_le_sinh, ← div_mul_eq_div_div_swap, self_le_sinh_iff]
  positivity
