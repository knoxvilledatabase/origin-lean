/-
Extracted from Probability/Distributions/Cauchy.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Cauchy Distribution over ℝ

Define the Cauchy distribution with location parameter `x₀` and scale parameter `γ`.

Note that we use "location" and "scale" to refer to these parameters in theorem names.

## Main definition

* `cauchyPDFReal`: the function `x₀ γ x ↦ π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹`,
  which is the probability density function of a Cauchy distribution with location parameter `x₀`
  and scale parameter `γ` (when `γ ≠ 0`).
* `cauchyPDF`: `ℝ≥0∞`-valued pdf, `cauchyPDF μ v x = ENNReal.ofReal (cauchyPDFReal μ v x)`.
* `cauchyMeasure`: a Cauchy measure on `ℝ`, parametrized by a location parameter `x₀ : ℝ` and a
  scale parameter `γ : ℝ≥0`.  If `γ = 0`, this is `dirac x₀`, otherwise it is defined as the
  measure with density `cauchyPDF x₀ γ` with respect to the Lebesgue measure.

-/

open scoped Real ENNReal NNReal

open MeasureTheory Measure

namespace ProbabilityTheory

section CauchyPDF

noncomputable def cauchyPDFReal (x₀ : ℝ) (γ : ℝ≥0) (x : ℝ) : ℝ :=
  π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹
