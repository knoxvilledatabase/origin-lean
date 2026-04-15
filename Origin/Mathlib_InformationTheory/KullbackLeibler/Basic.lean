/-
Extracted from InformationTheory/KullbackLeibler/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Kullback-Leibler divergence

The Kullback-Leibler divergence is a measure of the difference between two measures.

## Main definitions

* `klDiv μ ν`: Kullback-Leibler divergence between two measures, with value in `ℝ≥0∞`,
  defined as `∞` if `μ` is not absolutely continuous with respect to `ν` or
  if the log-likelihood ratio `llr μ ν` is not integrable with respect to `μ`, and by
  `ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real - μ.real univ)` otherwise.

Note that our Kullback-Leibler divergence is nonnegative by definition (it takes value in `ℝ≥0∞`).
However `∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ` is nonnegative for all finite
measures `μ ≪ ν`, as proved in the lemma `integral_llr_add_sub_measure_univ_nonneg`.
That lemma is our version of Gibbs' inequality ("the Kullback-Leibler divergence is nonnegative").

## Main statements

* `klDiv_eq_zero_iff` : the Kullback-Leibler divergence between two finite measures is zero if and
  only if the two measures are equal.

## Implementation details

The Kullback-Leibler divergence on probability measures is `∫ x, llr μ ν x ∂μ` if `μ ≪ ν`
(and the log-likelihood ratio is integrable) and `∞` otherwise.
The definition we use extends this to finite measures by introducing a correction term
`ν.real univ - μ.real univ`. The definition of the divergence thus uses the formula
`∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`, which is nonnegative for all finite
measures `μ ≪ ν`. This also makes `klDiv μ ν` equal to an f-divergence: it equals the integral
`∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν`, in which `klFun x = x * log x + 1 - x`.

-/

open Real MeasureTheory Set

open scoped ENNReal NNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

open Classical in

noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ
    then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ)
    else ∞

lemma klDiv_of_ac_of_integrable (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) :
    klDiv μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) := by
  rw [klDiv_def]
  exact if_pos ⟨h1, h2⟩
