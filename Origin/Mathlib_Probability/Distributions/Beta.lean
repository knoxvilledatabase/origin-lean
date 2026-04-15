/-
Extracted from Probability/Distributions/Beta.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Beta distributions over ℝ

Define the beta distribution over the reals.

## Main definitions
* `betaPDFReal`: the function `α β x ↦ (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)`
  for `0 < x ∧ x < 1` or `0` else, which is the probability density function of a beta distribution
  with shape parameters `α` and `β` (when `0 < α` and `0 < β`).
* `betaPDF`: `ℝ≥0∞`-valued pdf,
  `betaPDF α β = ENNReal.ofReal (betaPDFReal α β)`.
-/

open scoped ENNReal NNReal

open MeasureTheory Complex Set

namespace ProbabilityTheory

section BetaPDF

noncomputable def beta (α β : ℝ) : ℝ :=
  Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)

lemma beta_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 < beta α β :=
  div_pos (mul_pos (Real.Gamma_pos_of_pos hα) (Real.Gamma_pos_of_pos hβ))
    (Real.Gamma_pos_of_pos (add_pos hα hβ))

theorem beta_eq_betaIntegralReal (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    beta α β = (betaIntegral α β).re := by
  rw [betaIntegral_eq_Gamma_mul_div]
  · simp_rw [beta, ← ofReal_add α β, Gamma_ofReal]
    norm_cast
  all_goals simpa

noncomputable def betaPDFReal (α β x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then
    (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)
  else
    0

noncomputable def betaPDF (α β x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (betaPDFReal α β x)

lemma betaPDF_eq_zero_of_nonpos {α β x : ℝ} (hx : x ≤ 0) :
    betaPDF α β x = 0 := by
  simp [betaPDF_eq, hx.not_gt]

lemma betaPDF_eq_zero_of_one_le {α β x : ℝ} (hx : 1 ≤ x) :
    betaPDF α β x = 0 := by
  simp [betaPDF_eq, hx.not_gt]

lemma betaPDF_of_pos_lt_one {α β x : ℝ} (hx_pos : 0 < x) (hx_lt : x < 1) :
    betaPDF α β x = ENNReal.ofReal ((1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  rw [betaPDF_eq, if_pos ⟨hx_pos, hx_lt⟩]

lemma lintegral_betaPDF {α β : ℝ} :
    ∫⁻ x, betaPDF α β x =
      ∫⁻ (x : ℝ) in Ioo 0 1, ENNReal.ofReal (1 / beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  rw [← lintegral_add_compl _ measurableSet_Iic,
    setLIntegral_eq_zero measurableSet_Iic (fun x (hx : x ≤ 0) ↦ betaPDF_eq_zero_of_nonpos hx),
    zero_add, compl_Iic, ← lintegral_add_compl _ measurableSet_Ici,
    setLIntegral_eq_zero measurableSet_Ici (fun x (hx : 1 ≤ x) ↦ betaPDF_eq_zero_of_one_le hx),
    zero_add, compl_Ici, Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi,
    setLIntegral_congr_fun measurableSet_Ioo
      (fun x ⟨hx_pos, hx_lt⟩ ↦ betaPDF_of_pos_lt_one hx_pos hx_lt)]

lemma betaPDFReal_pos {α β x : ℝ} (hx1 : 0 < x) (hx2 : x < 1) (hα : 0 < α) (hβ : 0 < β) :
    0 < betaPDFReal α β x := by
  rw [betaPDFReal, if_pos ⟨hx1, hx2⟩]
  exact mul_pos (mul_pos (one_div_pos.2 (beta_pos hα hβ)) (Real.rpow_pos_of_pos hx1 (α - 1)))
    (Real.rpow_pos_of_pos (by linarith) (β - 1))
