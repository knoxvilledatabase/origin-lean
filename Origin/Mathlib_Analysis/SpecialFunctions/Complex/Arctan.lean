/-
Extracted from Analysis/SpecialFunctions/Complex/Arctan.lean
Genuine: 3 of 4 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Complex arctangent

This file defines the complex arctangent `Complex.arctan` as
$$\arctan z = -\frac i2 \log \frac{1 + zi}{1 - zi}$$
and shows that it extends `Real.arctan` to the complex plane. Its Taylor series expansion
$$\arctan z = \frac{(-1)^n}{2n + 1} z^{2n + 1},\ |z|<1$$
is proved in `Complex.hasSum_arctan`.
-/

namespace Complex

open scoped Real

noncomputable def arctan (z : ℂ) : ℂ := -I / 2 * log ((1 + z * I) / (1 - z * I))

theorem tan_arctan {z : ℂ} (h₁ : z ≠ I) (h₂ : z ≠ -I) : tan (arctan z) = z := by
  unfold tan sin cos
  rw [div_div_eq_mul_div, div_mul_cancel₀ _ two_ne_zero, ← div_mul_eq_mul_div,
    -- multiply top and bottom by `exp (arctan z * I)`
    ← mul_div_mul_right _ _ (exp_ne_zero (arctan z * I)), sub_mul, add_mul,
    ← exp_add, neg_mul, neg_add_cancel, exp_zero, ← exp_add, ← two_mul]
  have z₁ : 1 + z * I ≠ 0 := by
    contrapose h₁
    rw [add_eq_zero_iff_neg_eq, ← div_eq_iff I_ne_zero, div_I, neg_one_mul, neg_neg] at h₁
    exact h₁.symm
  have z₂ : 1 - z * I ≠ 0 := by
    contrapose h₂
    rw [sub_eq_zero, ← div_eq_iff I_ne_zero, div_I, one_mul] at h₂
    exact h₂.symm
  have key : exp (2 * (arctan z * I)) = (1 + z * I) / (1 - z * I) := by
    rw [arctan, ← mul_rotate, ← mul_assoc,
      show 2 * (I * (-I / 2)) = 1 by simp [field], one_mul, exp_log]
    · exact div_ne_zero z₁ z₂
  -- multiply top and bottom by `1 - z * I`
  rw [key, ← mul_div_mul_right _ _ z₂, sub_mul, add_mul, div_mul_cancel₀ _ z₂, one_mul,
    show _ / _ * I = -(I * I) * z by ring, I_mul_I, neg_neg, one_mul]

-- DISSOLVED: cos_ne_zero_of_arctan_bounds

set_option linter.flexible false in -- TODO: fix non-terminal simp

theorem arctan_tan {z : ℂ} (h₀ : z ≠ π / 2) (h₁ : -(π / 2) < z.re) (h₂ : z.re ≤ π / 2) :
    arctan (tan z) = z := by
  have h := cos_ne_zero_of_arctan_bounds h₀ h₁ h₂
  unfold arctan tan
  -- multiply top and bottom by `cos z`
  rw [← mul_div_mul_right (1 + _) _ h, add_mul, sub_mul, one_mul, ← mul_rotate, mul_div_cancel₀ _ h]
  conv_lhs =>
    enter [2, 1, 2]
    rw [sub_eq_add_neg, ← neg_mul, ← sin_neg, ← cos_neg]
  rw [← exp_mul_I, ← exp_mul_I, ← exp_sub, show z * I - -z * I = 2 * (I * z) by ring, log_exp,
    show -I / 2 * (2 * (I * z)) = -(I * I) * z by ring, I_mul_I, neg_neg, one_mul]
  all_goals simp
  · rwa [← div_lt_iff₀' two_pos, neg_div]
  · rwa [← le_div_iff₀' two_pos]
