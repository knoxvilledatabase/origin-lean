/-
Extracted from Probability/Distributions/Pareto.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Pareto distributions over ℝ

Define the Pareto measure over the reals.

## Main definitions
* `paretoPDFReal`: the function `t r x ↦ r * t ^ r * x ^ -(r + 1)`
  for `t ≤ x` or `0` else, which is the probability density function of a Pareto distribution with
  scale `t` and shape `r` (when `ht : 0 < t` and `hr : 0 < r`).
* `paretoPDF`: `ℝ≥0∞`-valued pdf,
  `paretoPDF t r = ENNReal.ofReal (paretoPDFReal t r)`.
* `paretoMeasure`: a Pareto measure on `ℝ`, parametrized by its scale `t` and shape `r`.

-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

variable {t r x : ℝ}

section ParetoPDF

noncomputable def paretoPDFReal (t r x : ℝ) : ℝ :=
  if t ≤ x then r * t ^ r * x ^ (-(r + 1)) else 0

noncomputable def paretoPDF (t r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (paretoPDFReal t r x)

lemma paretoPDF_of_lt (hx : x < t) : paretoPDF t r x = 0 := by
  simp only [paretoPDF_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

lemma paretoPDF_of_le (hx : t ≤ x) :
    paretoPDF t r x = ENNReal.ofReal (r * t ^ r * x ^ (-(r + 1))) := by
  simp only [paretoPDF_eq, if_pos hx]

lemma lintegral_paretoPDF_of_le (hx : x ≤ t) :
    ∫⁻ y in Iio x, paretoPDF t r y = 0 := by
  rw [setLIntegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · intro a (_ : a < _)
    simp only [paretoPDF_eq, ENNReal.ofReal_eq_zero]
    rw [if_neg (by linarith)]
