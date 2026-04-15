/-
Extracted from Analysis/Convex/SpecificFunctions/Basic.lean
Genuine: 9 | Conflates: 0 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination

/-!
# Collection of convex functions

In this file we prove that the following functions are convex or strictly convex:

* `strictConvexOn_exp` : The exponential function is strictly convex.
* `strictConcaveOn_log_Ioi`, `strictConcaveOn_log_Iio`: `Real.log` is strictly concave on
  $(0, +∞)$ and $(-∞, 0)$ respectively.
* `convexOn_rpow`, `strictConvexOn_rpow` : For `p : ℝ`, `fun x ↦ x ^ p` is convex on $[0, +∞)$ when
  `1 ≤ p` and strictly convex when `1 < p`.

The proofs in this file are deliberately elementary, *not* by appealing to the sign of the second
derivative. This is in order to keep this file early in the import hierarchy, since it is on the
path to Hölder's and Minkowski's inequalities and after that to Lp spaces and most of measure
theory.

(Strict) concavity of `fun x ↦ x ^ p` for `0 < p < 1` (`0 ≤ p ≤ 1`) can be found in
`Mathlib.Analysis.Convex.SpecificFunctions.Pow`.

## See also

`Mathlib.Analysis.Convex.Mul` for convexity of `x ↦ x ^ n`
-/

open Real Set NNReal

theorem strictConvexOn_exp : StrictConvexOn ℝ univ exp := by
  apply strictConvexOn_of_slope_strict_mono_adjacent convex_univ
  rintro x y z - - hxy hyz
  trans exp y
  · have h1 : 0 < y - x := by linarith
    have h2 : x - y < 0 := by linarith
    rw [div_lt_iff₀ h1]
    calc
      exp y - exp x = exp y - exp y * exp (x - y) := by rw [← exp_add]; ring_nf
      _ = exp y * (1 - exp (x - y)) := by ring
      _ < exp y * -(x - y) := by gcongr; linarith [add_one_lt_exp h2.ne]
      _ = exp y * (y - x) := by ring
  · have h1 : 0 < z - y := by linarith
    rw [lt_div_iff₀ h1]
    calc
      exp y * (z - y) < exp y * (exp (z - y) - 1) := by
        gcongr _ * ?_
        linarith [add_one_lt_exp h1.ne']
      _ = exp (z - y) * exp y - exp y := by ring
      _ ≤ exp z - exp y := by rw [← exp_add]; ring_nf; rfl

theorem convexOn_exp : ConvexOn ℝ univ exp :=
  strictConvexOn_exp.convexOn

theorem strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Ioi 0) log := by
  apply strictConcaveOn_of_slope_strict_anti_adjacent (convex_Ioi (0 : ℝ))
  intro x y z (hx : 0 < x) (hz : 0 < z) hxy hyz
  have hy : 0 < y := hx.trans hxy
  trans y⁻¹
  · have h : 0 < z - y := by linarith
    rw [div_lt_iff₀ h]
    have hyz' : 0 < z / y := by positivity
    have hyz'' : z / y ≠ 1 := by
      contrapose! h
      rw [div_eq_one_iff_eq hy.ne'] at h
      simp [h]
    calc
      log z - log y = log (z / y) := by rw [← log_div hz.ne' hy.ne']
      _ < z / y - 1 := log_lt_sub_one_of_pos hyz' hyz''
      _ = y⁻¹ * (z - y) := by field_simp
  · have h : 0 < y - x := by linarith
    rw [lt_div_iff₀ h]
    have hxy' : 0 < x / y := by positivity
    have hxy'' : x / y ≠ 1 := by
      contrapose! h
      rw [div_eq_one_iff_eq hy.ne'] at h
      simp [h]
    calc
      y⁻¹ * (y - x) = 1 - x / y := by field_simp
      _ < -log (x / y) := by linarith [log_lt_sub_one_of_pos hxy' hxy'']
      _ = -(log x - log y) := by rw [log_div hx.ne' hy.ne']
      _ = log y - log x := by ring

-- DISSOLVED: one_add_mul_self_lt_rpow_one_add

theorem one_add_mul_self_le_rpow_one_add {s : ℝ} (hs : -1 ≤ s) {p : ℝ} (hp : 1 ≤ p) :
    1 + p * s ≤ (1 + s) ^ p := by
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp
  by_cases hs' : s = 0
  · simp [hs']
  exact (one_add_mul_self_lt_rpow_one_add hs hs' hp).le

-- DISSOLVED: rpow_one_add_lt_one_add_mul_self

theorem rpow_one_add_le_one_add_mul_self {s : ℝ} (hs : -1 ≤ s) {p : ℝ} (hp1 : 0 ≤ p) (hp2 : p ≤ 1) :
    (1 + s) ^ p ≤ 1 + p * s := by
  rcases eq_or_lt_of_le hp1 with (rfl | hp1)
  · simp
  rcases eq_or_lt_of_le hp2 with (rfl | hp2)
  · simp
  by_cases hs' : s = 0
  · simp [hs']
  exact (rpow_one_add_lt_one_add_mul_self hs hs' hp1 hp2).le

theorem strictConvexOn_rpow {p : ℝ} (hp : 1 < p) : StrictConvexOn ℝ (Ici 0) fun x : ℝ ↦ x ^ p := by
  apply strictConvexOn_of_slope_strict_mono_adjacent (convex_Ici (0 : ℝ))
  intro x y z (hx : 0 ≤ x) (hz : 0 ≤ z) hxy hyz
  have hy : 0 < y := hx.trans_lt hxy
  have hy' : 0 < y ^ p := rpow_pos_of_pos hy _
  trans p * y ^ (p - 1)
  · have q : 0 < y - x := by rwa [sub_pos]
    rw [div_lt_iff₀ q, ← div_lt_div_iff_of_pos_right hy', _root_.sub_div, div_self hy'.ne',
      ← div_rpow hx hy.le, sub_lt_comm, ← add_sub_cancel_right (x / y) 1, add_comm, add_sub_assoc,
      ← div_mul_eq_mul_div, mul_div_assoc, ← rpow_sub hy, sub_sub_cancel_left, rpow_neg_one,
      mul_assoc, ← div_eq_inv_mul, sub_eq_add_neg, ← mul_neg, ← neg_div, neg_sub, _root_.sub_div,
      div_self hy.ne']
    apply one_add_mul_self_lt_rpow_one_add _ _ hp
    · rw [le_sub_iff_add_le, neg_add_cancel, div_nonneg_iff]
      exact Or.inl ⟨hx, hy.le⟩
    · rw [sub_ne_zero]
      exact ((div_lt_one hy).mpr hxy).ne
  · have q : 0 < z - y := by rwa [sub_pos]
    rw [lt_div_iff₀ q, ← div_lt_div_iff_of_pos_right hy', _root_.sub_div, div_self hy'.ne',
      ← div_rpow hz hy.le, lt_sub_iff_add_lt', ← add_sub_cancel_right (z / y) 1, add_comm _ 1,
      add_sub_assoc, ← div_mul_eq_mul_div, mul_div_assoc, ← rpow_sub hy, sub_sub_cancel_left,
      rpow_neg_one, mul_assoc, ← div_eq_inv_mul, _root_.sub_div, div_self hy.ne']
    apply one_add_mul_self_lt_rpow_one_add _ _ hp
    · rw [le_sub_iff_add_le, neg_add_cancel, div_nonneg_iff]
      exact Or.inl ⟨hz, hy.le⟩
    · rw [sub_ne_zero]
      exact ((one_lt_div hy).mpr hyz).ne'

theorem convexOn_rpow {p : ℝ} (hp : 1 ≤ p) : ConvexOn ℝ (Ici 0) fun x : ℝ ↦ x ^ p := by
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simpa using convexOn_id (convex_Ici _)
  exact (strictConvexOn_rpow hp).convexOn

theorem strictConcaveOn_log_Iio : StrictConcaveOn ℝ (Iio 0) log := by
  refine ⟨convex_Iio _, ?_⟩
  intro x (hx : x < 0) y (hy : y < 0) hxy a b ha hb hab
  have hx' : 0 < -x := by linarith
  have hy' : 0 < -y := by linarith
  have hxy' : -x ≠ -y := by contrapose! hxy; linarith
  calc
    a • log x + b • log y = a • log (-x) + b • log (-y) := by simp_rw [log_neg_eq_log]
    _ < log (a • -x + b • -y) := strictConcaveOn_log_Ioi.2 hx' hy' hxy' ha hb hab
    _ = log (-(a • x + b • y)) := by congr 1; simp only [Algebra.id.smul_eq_mul]; ring
    _ = _ := by rw [log_neg_eq_log]

namespace Real

lemma exp_mul_le_cosh_add_mul_sinh {t : ℝ} (ht : |t| ≤ 1) (x : ℝ) :
    exp (t * x) ≤ cosh x + t * sinh x := by
  rw [abs_le] at ht
  calc
    _ = exp ((1 + t) / 2 * x + (1 - t) / 2 * (-x)) := by ring_nf
    _ ≤ (1 + t) / 2 * exp x + (1 - t) / 2 * exp (-x) :=
        convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) <| by ring
    _ = _ := by rw [cosh_eq, sinh_eq]; ring

end Real
