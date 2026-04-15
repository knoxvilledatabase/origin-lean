/-
Extracted from Probability/Distributions/Poisson/Basic.lean
Genuine: 9 of 10 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Poisson distributions over ℕ

Define the Poisson measure over the natural numbers. For `r : ℝ≥0`, `poissonMeasure r` is the
measure which to `{n}` associates `exp (-r) * r ^ n / (n)!`.

## Main definition

* `poissonMeasure r`: a Poisson measure on `ℕ`, parametrized by its rate `r : ℝ≥0`.
-/

open MeasureTheory Real

open scoped NNReal Nat

namespace ProbabilityTheory

noncomputable

def poissonMeasure (r : ℝ≥0) : Measure ℕ :=
  Measure.sum (fun n ↦ ENNReal.ofReal (exp (-r) * r ^ n / (n)!) • (.dirac n))

lemma poissonMeasure_singleton (r : ℝ≥0) (n : ℕ) :
    (poissonMeasure r) {n} = ENNReal.ofReal (exp (-r) * r ^ n / (n)!) := by
  rw [poissonMeasure, Measure.sum_smul_dirac_singleton]

lemma poissonMeasure_real_singleton (r : ℝ≥0) (n : ℕ) :
    (poissonMeasure r).real {n} = exp (-r) * r ^ n / (n)! := by
  rw [measureReal_def, poissonMeasure_singleton, ENNReal.toReal_ofReal (by positivity)]

lemma poissonMeasure_real_singleton_pos {r : ℝ≥0} (n : ℕ) (hr : 0 < r) :
    0 < (poissonMeasure r).real {n} := by
  rw [poissonMeasure_real_singleton]
  positivity

lemma hasSum_one_poissonMeasure (r : ℝ≥0) : HasSum (fun n ↦ exp (-r) * r ^ n / (n)!) 1 := by
  convert (NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).mul_left (exp (-r)) using 1
  · simp_rw [mul_div_assoc]
  · simp [← exp_eq_exp_ℝ, ← exp_add]

-- INSTANCE (free from Core): isProbabilityMeasure_poissonMeasure

section Integral

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_poissonMeasure_iff {r : ℝ≥0} {f : ℕ → E} :
    Integrable f (poissonMeasure r) ↔ Summable (fun n ↦ exp (-r) * r ^ n / (n)! * ‖f n‖) := by
  rw [poissonMeasure, integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n ↦ ?_ * _)
  rw [ENNReal.toReal_ofReal (by positivity)]

variable [NormedSpace ℝ E]

lemma hasSum_integral_poissonMeasure [CompleteSpace E] {r : ℝ≥0} {f : ℕ → E}
    (hf : Integrable f (poissonMeasure r)) :
    HasSum (fun n ↦ (exp (-r) * r ^ n / (n)!) • f n) (∫ n, f n ∂poissonMeasure r) := by
  have : (fun n ↦ (exp (-r) * r ^ n / (n)!) • f n) =
      fun n ↦ (ENNReal.ofReal (exp (-r) * r ^ n / (n)!)).toReal • f n := by
    ext; rw [ENNReal.toReal_ofReal (by positivity)]
  rw [this]
  apply hasSum_integral_sum_dirac (by simp)
  convert integrable_poissonMeasure_iff.1 hf
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma integral_poissonMeasure' [CompleteSpace E] {r : ℝ≥0} {f : ℕ → E}
    (hf : Integrable f (poissonMeasure r)) :
    ∫ n, f n ∂poissonMeasure r = ∑' n, (exp (-r) * r ^ n / (n)!) • f n :=
  (hasSum_integral_poissonMeasure hf).tsum_eq.symm

lemma integral_poissonMeasure [FiniteDimensional ℝ E] (r : ℝ≥0) (f : ℕ → E) :
    ∫ n, f n ∂poissonMeasure r = ∑' n, (exp (-r) * r ^ n / (n)!) • f n := by
  rw [poissonMeasure, integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (by positivity)]

end Integral

section PoissonPMF
