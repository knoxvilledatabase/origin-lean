/-
Extracted from Analysis/SpecialFunctions/Trigonometric/Chebyshev/RootsExtrema.lean
Genuine: 13 of 29 | Dissolved: 16 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chebyshev polynomials over the reals: roots and extrema

## Main statements

* `T_n(x) ∈ [-1, 1]` iff `x ∈ [-1, 1]`: `abs_eval_T_real_le_one_iff`
* Zeroes of `T` and `U`: `roots_T_real`, `roots_U_real`
* Local extrema of `T`: `isLocalExtr_T_real_iff`, `isExtrOn_T_real_iff`
* Irrationality of zeroes of `T` other than zero: `irrational_of_isRoot_T_real`
* `|T_n^{(k)} (x)| ≤ T_n^{(k)} (1)` for `x ∈ [-1, 1]`: `abs_iterate_derivative_T_real_le`

## TODO

Show that the bound on `T_n^{(k)} (x)` is achieved only at `x = ±1`
-/

namespace Polynomial.Chebyshev

open Real

theorem eval_T_real_mem_Icc (n : ℤ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    (T ℝ n).eval x ∈ Set.Icc (-1) 1 := by
  rw [← cos_arccos (x := x) (by grind) (by grind)]
  grind [T_real_cos, cos_mem_Icc]

theorem abs_eval_T_real_le_one (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(T ℝ n).eval x| ≤ 1 := by grind [eval_T_real_mem_Icc]

theorem one_le_eval_T_real (n : ℤ) {x : ℝ} (hx : 1 ≤ x) : 1 ≤ (T ℝ n).eval x := by
  rw [← cosh_arcosh hx]
  grind [T_real_cosh, one_le_cosh]

-- DISSOLVED: one_lt_eval_T_real

theorem one_le_negOnePow_mul_eval_T_real (n : ℤ) {x : ℝ} (hx : x ≤ -1) :
    1 ≤ n.negOnePow * (T ℝ n).eval x := by
  rw [← neg_neg x, T_eval_neg]
  convert one_le_eval_T_real n (le_neg_of_le_neg hx)
  rw [Int.cast_negOnePow, ← mul_assoc, ← mul_zpow]
  simp

-- DISSOLVED: one_lt_negOnePow_mul_eval_T_real

theorem one_le_abs_eval_T_real (n : ℤ) {x : ℝ} (hx : 1 ≤ |x|) :
    1 ≤ |(T ℝ n).eval x| := by
  wlog! h : 0 ≤ x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n (-x) (by grind) (by grind)
  · exact one_le_eval_T_real n (abs_of_nonneg h ▸ hx) |>.trans <| le_abs_self _

-- DISSOLVED: one_lt_abs_eval_T_real

-- DISSOLVED: abs_eval_T_real_le_one_iff

-- DISSOLVED: abs_eval_T_real_eq_one_iff

-- DISSOLVED: eval_T_real_cos_int_mul_pi_div

-- DISSOLVED: eval_T_real_eq_one_iff

-- DISSOLVED: eval_T_real_eq_neg_one_iff

theorem roots_T_real_nodup (n : ℕ) :
    (Multiset.map (fun k : ℕ ↦ cos ((2 * k + 1) * π / (2 * n))) (.range n)).Nodup := by
  wlog! hn : n ≠ 0
  · simp [hn]
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  refine injOn_cos.comp (by aesop) fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
  field_simp
  norm_cast
  grind

theorem roots_T_real (n : ℕ) :
    (T ℝ n).roots =
    ((Finset.range n).image (fun (k : ℕ) => cos ((2 * k + 1) * π / (2 * n)))).val := by
  wlog! hn : n ≠ 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    rw [← hx, T_real_cos, cos_eq_zero_iff]
    use k
    field_simp
    norm_cast
  · rw [Finset.card_image_of_injOn, Finset.card_range, degree_T, Int.natAbs_natCast]
    exact (Finset.range n).nodup_map_iff_injOn.mp (roots_T_real_nodup n)

theorem rootMultiplicity_T_real {n k : ℕ} (hk : k < n) :
    (T ℝ n).rootMultiplicity (cos ((2 * k + 1) * π / (2 * n))) = 1 := by
  rw [← count_roots, roots_T_real, Multiset.count_eq_one_of_mem (by simp)]
  grind

theorem roots_U_real_nodup (n : ℕ) :
    (Multiset.map (fun k : ℕ ↦ cos ((k + 1) * π / (n + 1))) (.range n)).Nodup := by
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  apply injOn_cos.comp
  · intro x hx y hy hxy
    field_simp at hxy
    aesop
  · refine fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
    field_simp
    norm_cast
    grind

theorem roots_U_real (n : ℕ) :
    (U ℝ n).roots =
    ((Finset.range n).image (fun (k : ℕ) => cos ((k + 1) * π / (n + 1)))).val := by
  wlog! hn : n ≠ 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    suffices (U ℝ n).eval x * sin ((k + 1) * π / (n + 1)) = 0 by
      refine (mul_eq_zero_iff_right (ne_of_gt (sin_pos_of_pos_of_lt_pi (by positivity) ?_))).mp this
      field_simp
      norm_cast
      grind
    rw [← hx, U_real_cos, sin_eq_zero_iff]
    use k + 1
    field_simp
    norm_cast
    ring
  · rw [Finset.card_image_of_injOn, Finset.card_range, degree_U_natCast]
    exact (Finset.range n).nodup_map_iff_injOn.mp (roots_U_real_nodup n)

theorem rootMultiplicity_U_real {n k : ℕ} (hk : k < n) :
    (U ℝ n).rootMultiplicity (cos ((k + 1) * π / (n + 1))) = 1 := by
  rw [← count_roots, roots_U_real, Multiset.count_eq_one_of_mem (by simp)]
  grind

-- DISSOLVED: isLocalMax_T_real

-- DISSOLVED: isLocalMin_T_real

-- DISSOLVED: isLocalExtr_T_real

theorem isLocalExtr_T_real_iff {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    IsLocalExtr (T ℝ n).eval x ↔ ∃ k ∈ Finset.Ioo 0 n, x = cos (k * π / n) := by
  constructor
  · intro hx
    replace hx := hx.deriv_eq_zero
    rw [Polynomial.deriv, T_derivative_eq_U, eval_mul, Int.cast_natCast, eval_natCast,
      mul_eq_zero_iff_left (by aesop)] at hx
    replace hx : x ∈ (U ℝ (n - 1)).roots :=
      (mem_roots (degree_ne_bot.mp (ne_of_eq_of_ne (by grind [degree_U_natCast])
        (WithBot.natCast_ne_bot (n - 1))))).mpr hx
    rw [show (n - 1 : ℤ) = (n - 1 : ℕ) by grind, roots_U_real, Finset.mem_val] at hx
    obtain ⟨k, hk₁, hx⟩ := Finset.mem_image.mp hx
    refine ⟨k + 1, Finset.mem_Ioo.mpr ⟨k.zero_lt_succ, by grind⟩, ?_⟩
    rw [← hx]
    congr <;> norm_cast
    exact Nat.sub_add_cancel (Nat.one_le_of_lt hn)
  · rintro ⟨k, hk, hx⟩
    rw [hx]
    exact isLocalExtr_T_real (Nat.ne_zero_of_lt hn)
      (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2

-- DISSOLVED: isMaxOn_T_real

-- DISSOLVED: isMinOn_T_real

-- DISSOLVED: isExtrOn_T_real

-- DISSOLVED: isExtrOn_T_real_iff

-- DISSOLVED: irrational_of_isRoot_T_real

theorem abs_iterate_derivative_T_real_le (n : ℤ) (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(derivative^[k] (T ℝ n)).eval x| ≤ (derivative^[k] (T ℝ n)).eval 1 := by
  wlog hn : 0 ≤ n
  · convert this (-n) k hx (by grind) using 1 <;> rw [T_neg]
  lift n to ℕ using hn
  have := T_iterate_derivative_mem_span_T (R := ℝ) n k
  obtain ⟨f, hfsupp, hfderiv⟩ := Submodule.mem_span_set.mp this
  replace hfderiv : ∑ p ∈ f.support, f p • p = derivative^[k] (T ℝ n) := by rw [← hfderiv]; rfl
  have hf (y : ℝ) :
      ∑ p ∈ f.support, f p • p.eval y = (derivative^[k] (T ℝ n)).eval y := by
    rw [← hfderiv, Polynomial.eval_finset_sum]
    simp_rw [Polynomial.eval_smul]
  rw [← hf x, ← hf 1]
  grw [Finset.abs_sum_le_sum_abs]
  refine Finset.sum_le_sum (fun i hi => ?_)
  obtain ⟨m, hm, hi⟩ := (Set.mem_image ..).mp (hfsupp hi)
  grw [abs_nsmul, ← hi, abs_eval_T_real_le_one m hx]
  simp

end Polynomial.Chebyshev
