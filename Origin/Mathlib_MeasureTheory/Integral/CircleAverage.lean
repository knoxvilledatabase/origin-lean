/-
Extracted from MeasureTheory/Integral/CircleAverage.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Circle Averages

For a function `f` on the complex plane, this file introduces the definition
`Real.circleAverage f c R` as a shorthand for the average of `f` on the circle with center `c` and
radius `R`, equipped with the rotation-invariant measure of total volume one. Like
`IntervalAverage`, this notion exists as a convenience. It avoids notationally inconvenient
compositions of `f` with `circleMap` and avoids the need to manually eliminate `2 * π` every time
an average is computed.

Note: Like the interval average defined in `Mathlib/MeasureTheory/Integral/IntervalAverage.lean`,
the `circleAverage` defined here is a purely measure-theoretic average. It should not be confused
with `circleIntegral`, which is the path integral over the circle path. The relevant integrability
property `circleAverage` is `CircleIntegrable`, as defined in
`Mathlib/MeasureTheory/Integral/CircleIntegral.lean`.

Implementation Note: Like `circleMap`, `circleAverage`s are defined for negative radii. The theorem
`circleAverage_congr_negRadius` shows that the average is independent of the radius' sign.
-/

open Complex Filter Metric Real Set Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  {f f₁ f₂ : ℂ → E} {c : ℂ} {R : ℝ} {a : 𝕜}

namespace Real

/-!
### Definition
-/

variable (f c R) in

noncomputable def circleAverage : E :=
  (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ)

theorem circleAverage.integral_undef (hf : ¬CircleIntegrable f c R) :
    circleAverage f c R = 0 := by
  simp_all [circleAverage, CircleIntegrable, intervalIntegral.integral_undef]

lemma circleAverage_eq_intervalAverage :
    circleAverage f c R = ⨍ θ in 0..2 * π, f (circleMap c R θ) := by
  simp [circleAverage, interval_average_eq]
