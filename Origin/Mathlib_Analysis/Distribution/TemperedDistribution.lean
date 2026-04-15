/-
Extracted from Analysis/Distribution/TemperedDistribution.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# TemperedDistribution

## Main definitions

* `TemperedDistribution E F`: The space `𝓢(E, ℂ) →L[ℂ] F` equipped with the pointwise
  convergence topology.
* `MeasureTheory.Measure.toTemperedDistribution`: Every measure of temperate growth is a tempered
  distribution.
* `Function.HasTemperateGrowth.toTemperedDistribution`: Every function of temperate growth is a
  tempered distribution.
* `SchwartzMap.toTemperedDistributionCLM`: The canonical map from `𝓢` to `𝓢'` as a continuous linear
  map.
* `MeasureTheory.Lp.toTemperedDistribution`: Every `Lp` function is a tempered distribution.
* `TemperedDistribution.mulLeftCLM`: Multiplication with temperate growth function as a continuous
  linear map.
* `TemperedDistribution.instLineDeriv`: The directional derivative on tempered distributions.
* `TemperedDistribution.fourierTransformCLM`: The Fourier transform on tempered distributions.

## Notation
* `𝓢'(E, F)`: The space of tempered distributions `TemperedDistribution E F` scoped in
  `SchwartzMap`
-/

open SchwartzMap ContinuousLinearMap MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {ι 𝕜 E F F₁ F₂ : Type*}

section definition

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

variable (E F) in

abbrev TemperedDistribution := 𝓢(E, ℂ) →Lₚₜ[ℂ] F
