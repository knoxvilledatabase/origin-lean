/-
Extracted from Probability/Distributions/Gaussian/Real.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Gaussian distributions over ℝ

We define a Gaussian measure over the reals.

## Main definitions

* `gaussianPDFReal`: the function `μ v x ↦ (1 / (sqrt (2 * pi * v))) * exp (- (x - μ)^2 / (2 * v))`,
  which is the probability density function of a Gaussian distribution with mean `μ` and
  variance `v` (when `v ≠ 0`).
* `gaussianPDF`: `ℝ≥0∞`-valued pdf, `gaussianPDF μ v x = ENNReal.ofReal (gaussianPDFReal μ v x)`.
* `gaussianReal`: a Gaussian measure on `ℝ`, parametrized by its mean `μ` and variance `v`.
  If `v = 0`, this is `dirac μ`, otherwise it is defined as the measure with density
  `gaussianPDF μ v` with respect to the Lebesgue measure.

## Main results

* `gaussianReal_add_const`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `X + y` is Gaussian with mean `μ + y` and variance `v`.
* `gaussianReal_const_mul`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `c * X` is Gaussian with mean `c * μ` and variance `c ^ 2 * v`.

-/

open scoped ENNReal NNReal Real Complex

open MeasureTheory

namespace ProbabilityTheory

section GaussianPDF

noncomputable

def gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))
