/-
Extracted from MeasureTheory/Integral/IntervalAverage.lean
Genuine: 5 of 7 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integral average over an interval

In this file we introduce notation `⨍ x in a..b, f x` for the average `⨍ x in Ι a b, f x` of `f`
over the interval `Ι a b = Set.Ioc (min a b) (max a b)` w.r.t. the Lebesgue measure, then prove
formulas for this average:

* `interval_average_eq`: `⨍ x in a..b, f x = (b - a)⁻¹ • ∫ x in a..b, f x`;
* `interval_average_eq_div`: `⨍ x in a..b, f x = (∫ x in a..b, f x) / (b - a)`;
* `exists_eq_interval_average_of_measure`:
    `∃ c ∈ Ι a b, f c = ⨍ x in Ι a b, f x ∂μ`.
* `exists_eq_interval_average_of_noAtoms`:
    `∃ c ∈ uIoo a b, f c = ⨍ x in Ι a b, f x ∂μ`.
* `exists_eq_interval_average`:
    `∃ c ∈ uIoo a b, f c = ⨍ x in a..b, f x`.

We also prove that `⨍ x in a..b, f x = ⨍ x in b..a, f x`, see `interval_average_symm`.

## Notation

`⨍ x in a..b, f x`: average of `f` over the interval `Ι a b` w.r.t. the Lebesgue measure.

-/

open MeasureTheory Set intervalIntegral

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

notation3 "⨍ "(...)" in "a".."b",

  "r:60:(scoped f => average (Measure.restrict volume (uIoc a b)) f) => r

theorem interval_average_symm (f : ℝ → E) (a b : ℝ) : (⨍ x in a..b, f x) = ⨍ x in b..a, f x := by
  rw [setAverage_eq, setAverage_eq, uIoc_comm]

theorem interval_average_eq (f : ℝ → E) (a b : ℝ) :
    (⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x := by
  rcases le_or_gt a b with h | h
  · rw [setAverage_eq, uIoc_of_le h, Real.volume_real_Ioc_of_le h, integral_of_le h]
  · rw [setAverage_eq, uIoc_of_ge h.le, Real.volume_real_Ioc_of_le h.le, integral_of_ge h.le,
      smul_neg, ← neg_smul, ← inv_neg, neg_sub]

theorem interval_average_eq_div (f : ℝ → ℝ) (a b : ℝ) :
    (⨍ x in a..b, f x) = (∫ x in a..b, f x) / (b - a) := by
  rw [interval_average_eq, smul_eq_mul, div_eq_inv_mul]

theorem intervalAverage_congr_codiscreteWithin {a b : ℝ} {f₁ f₂ : ℝ → ℝ}
    (hf : f₁ =ᶠ[Filter.codiscreteWithin (Ι a b)] f₂) :
    ⨍ (x : ℝ) in a..b, f₁ x = ⨍ (x : ℝ) in a..b, f₂ x := by
  rw [interval_average_eq, integral_congr_codiscreteWithin hf, ← interval_average_eq]

variable {f : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ}

-- DISSOLVED: exists_eq_interval_average_of_measure

-- DISSOLVED: exists_eq_interval_average_of_noAtoms

theorem exists_eq_interval_average
    (hab : a ≠ b) (hf : ContinuousOn f (uIcc a b)) :
    ∃ c ∈ uIoo a b, f c = ⨍ x in a..b, f x :=
  exists_eq_interval_average_of_noAtoms hf (by simp) (by simpa using sub_ne_zero.mpr hab.symm)
