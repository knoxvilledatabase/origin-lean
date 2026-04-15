/-
Extracted from Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integral representations of `rpow`

This file contains an integral representation of the `rpow` function between 0 and 1: we show
that there exists a measure on ℝ such that `x ^ p = ∫ t, rpowIntegrand₀₁ p t x ∂μ` for
the integrand `rpowIntegrand₀₁ p t x := t ^ p * (t⁻¹ - (t + x)⁻¹)`.

This representation is useful for showing that `rpow` is operator monotone and operator concave
in this range; that is, `cfc rpow` is monotone/concave. The integrand can be shown to be
operator monotone and concave through direct means, and this integral lifts these properties
to `rpow`. These results can be found in
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order`.

## Notes

Here we only compute the integral up to a constant, even though the actual constant can be
computed via contour integration. We chose to avoid this, as the constant is seldom if ever
relevant in applications, and would needlessly complicate the proof.

## Main declarations

+ `rpowIntegrand₀₁ p t x := t ^ p * (t⁻¹ - (t + x)⁻¹)`
+ `rpowIntegrand₁₂ p t x := t ^ (p - 1) * (x * t⁻¹ + t * (t + x)⁻¹ - 1)`
+ `exists_measure_rpow_eq_integral_rpowIntegrand₀₁` and
  `exists_measure_rpow_eq_integral_rpowIntegrand₁₂`: there exists a measure on `ℝ` such that
  `x ^ p = ∫ t, rpowIntegrand₀₁ p t x ∂μ` (resp `x ^ p = ∫ t, rpowIntegrand₁₂ p t x ∂μ`)
+ `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁` and
  `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂`: the corresponding statements where
  `x ^ p` is defined via the CFC.

## TODO

+ Give analogous representations for the range `Ioo (-1) 0`.

## References

+ [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An introductory course"
  (see Lemma 2.8)
-/

open MeasureTheory Set Filter

open scoped NNReal Topology

namespace Real

noncomputable def rpowIntegrand₀₁ (p t x : ℝ) : ℝ := t ^ p * (t⁻¹ - (t + x)⁻¹)

noncomputable def rpowIntegrand₁₂ (p t x : ℝ) : ℝ := t ^ (p - 1) * (t⁻¹ * x + t * (t + x)⁻¹ - 1)

section ZeroOne

variable {p t x : ℝ}
