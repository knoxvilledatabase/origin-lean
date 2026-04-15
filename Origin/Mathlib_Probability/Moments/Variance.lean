/-
Extracted from Probability/Moments/Variance.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Variance of random variables

We define the variance of a real-valued random variable as `Var[X] = 𝔼[(X - 𝔼[X])^2]` (in the
`ProbabilityTheory` locale).

## Main definitions

* `ProbabilityTheory.evariance`: the variance of a real-valued random variable as an extended
  non-negative real.
* `ProbabilityTheory.variance`: the variance of a real-valued random variable as a real number.

## Main results

* `ProbabilityTheory.variance_le_expectation_sq`: the inequality `Var[X] ≤ 𝔼[X^2]`.
* `ProbabilityTheory.meas_ge_le_variance_div_sq`: Chebyshev's inequality, i.e.,
      `ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ENNReal.ofReal (Var[X] / c ^ 2)`.
* `ProbabilityTheory.meas_ge_le_evariance_div_sq`: Chebyshev's inequality formulated with
  `evariance` without requiring the random variables to be L².
* `ProbabilityTheory.IndepFun.variance_add`: the variance of the sum of two independent
  random variables is the sum of the variances.
* `ProbabilityTheory.IndepFun.variance_sum`: the variance of a finite sum of pairwise
  independent random variables is the sum of the variances.
* `ProbabilityTheory.variance_le_sub_mul_sub`: the variance of a random variable `X` satisfying
  `a ≤ X ≤ b` almost everywhere is at most `(b - 𝔼 X) * (𝔼 X - a)`.
* `ProbabilityTheory.variance_le_sq_of_bounded`: the variance of a random variable `X` satisfying
  `a ≤ X ≤ b` almost everywhere is at most `((b - a) / 2) ^ 2`.
-/

open MeasureTheory Filter Finset

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω}

variable (X μ) in

def evariance : ℝ≥0∞ := ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ

variable (X μ) in

def variance : ℝ := (evariance X μ).toReal

scoped notation "eVar[" X "; " μ "]" => ProbabilityTheory.evariance X μ

scoped notation "eVar[" X "]" => eVar[X; MeasureTheory.MeasureSpace.volume]

scoped notation "Var[" X "; " μ "]" => ProbabilityTheory.variance X μ

scoped notation "Var[" X "]" => Var[X; MeasureTheory.MeasureSpace.volume]

theorem evariance_congr (h : X =ᵐ[μ] Y) : eVar[X; μ] = eVar[Y; μ] := by
  simp_rw [evariance, integral_congr_ae h]
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω using by simp [hω]

theorem variance_congr (h : X =ᵐ[μ] Y) : Var[X; μ] = Var[Y; μ] := by
  simp_rw [variance, evariance_congr h]
