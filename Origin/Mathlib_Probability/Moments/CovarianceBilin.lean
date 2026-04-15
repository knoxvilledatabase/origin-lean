/-
Extracted from Probability/Moments/CovarianceBilin.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Covariance in Hilbert spaces

Given a measure `μ` defined over a Banach space `E`, one can consider the associated covariance
bilinear form which maps `L₁ L₂ : StrongDual ℝ E` to `cov[L₁, L₂; μ]`. This is called
`covarianceBilinDual μ` and is defined in the `CovarianceBilinDual` file.

In the special case where `E` is a Hilbert space, each `L : StrongDual ℝ E` can be represented
as the scalar product against some element of `E`. This motivates the definition of
`covarianceBilin`, which is a continuous bilinear form mapping `x y : E` to
`cov[⟪x, ·⟫, ⟪y, ·⟫; μ]`.

## Main definitions

* `covarianceBilin μ`: the continuous bilinear form over `E` representing the covariance of a
  measure over `E`.
* `covarianceOperator μ`: the bounded operator over `E` such that
  `⟪covarianceOperator μ x, y⟫ = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ`.

## Tags

covariance, Hilbert space, bilinear form
-/

open MeasureTheory InnerProductSpace NormedSpace WithLp EuclideanSpace

open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

noncomputable

def covarianceBilin (μ : Measure E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (covarianceBilinDual μ)
    (toDualMap ℝ E).toContinuousLinearMap (toDualMap ℝ E).toContinuousLinearMap
