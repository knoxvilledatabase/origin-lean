/-
Extracted from Probability/Distributions/Gaussian/Multivariate.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Multivariate Gaussian distributions

In this file we define the standard Gaussian distribution over a Euclidean space and multivariate
Gaussian distributions over `EuclideanSpace ℝ ι`.

## Main definitions

* `stdGaussian E`: Standard Gaussian distribution on a finite-dimensional real inner product space
  `E`. This is the random vector whose coordinates in an orthonormal basis are independent standard
  Gaussian.
* `multivariateGaussian μ S`: The multivariate Gaussian distribution on `EuclideanSpace ℝ ι`
  with mean `μ` and covariance matrix `S`, when `S` is a positive semidefinite matrix.

## TODO

- Generalize `multivariateGaussian μ S` when `S` is a symmetric trace class operator over a
  Hilbert space.

## Tags

multivariate Gaussian distribution

-/

open MeasureTheory Matrix WithLp Module Complex

open scoped RealInnerProductSpace MatrixOrder

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

section stdGaussian

/-! ### Standard Gaussian measure over a Euclidean space -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

variable (E) in

noncomputable

def stdGaussian : Measure E :=
  (Measure.pi (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1)).map
    (fun x ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i)

variable [BorelSpace E]

-- INSTANCE (free from Core): isProbabilityMeasure_stdGaussian
