/-
Extracted from Probability/Distributions/Exponential.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Exponential distributions over ℝ

Define the Exponential measure over the reals.

## Main definitions
* `exponentialPDFReal`: the function `r x ↦ r * exp (-(r * x)` for `0 ≤ x`
  or `0` else, which is the probability density function of an exponential distribution with
  rate `r` (when `hr : 0 < r`).
* `exponentialPDF`: `ℝ≥0∞`-valued pdf,
  `exponentialPDF r = ENNReal.ofReal (exponentialPDFReal r)`.
* `expMeasure`: an exponential measure on `ℝ`, parametrized by its rate `r`.

## Main results
* `cdf_expMeasure_eq`: Proof that the CDF of the exponential measure equals the
  known function given as `r x ↦ 1 - exp (- (r * x))` for `0 ≤ x` or `0` else.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section ExponentialPDF

noncomputable

def exponentialPDFReal (r x : ℝ) : ℝ :=
  gammaPDFReal 1 r x

noncomputable

def exponentialPDF (r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (exponentialPDFReal r x)

lemma exponentialPDF_eq (r x : ℝ) :
    exponentialPDF r x = ENNReal.ofReal (if 0 ≤ x then r * exp (-(r * x)) else 0) := by
  rw [exponentialPDF, exponentialPDFReal, gammaPDFReal]
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]

lemma exponentialPDF_of_neg {r x : ℝ} (hx : x < 0) : exponentialPDF r x = 0 := gammaPDF_of_neg hx

lemma exponentialPDF_of_nonneg {r x : ℝ} (hx : 0 ≤ x) :
    exponentialPDF r x = ENNReal.ofReal (r * rexp (-(r * x))) := by
  simp only [exponentialPDF_eq, if_pos hx]

lemma lintegral_exponentialPDF_of_nonpos {x r : ℝ} (hx : x ≤ 0) :
    ∫⁻ y in Iio x, exponentialPDF r y = 0 := lintegral_gammaPDF_of_nonpos hx
