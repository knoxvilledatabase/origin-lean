/-
Extracted from MeasureTheory/Measure/LogLikelihoodRatio.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Log-likelihood Ratio

The likelihood ratio between two measures `μ` and `ν` is their Radon-Nikodym derivative
`μ.rnDeriv ν`. The logarithm of that function is often used instead: this is the log-likelihood
ratio.

This file contains a definition of the log-likelihood ratio (llr) and its properties.

## Main definitions

* `llr μ ν`: Log-Likelihood Ratio between `μ` and `ν`, defined as the function
  `x ↦ log (μ.rnDeriv ν x).toReal`.

-/

open Real

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {f : α → ℝ}

noncomputable def llr (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal

lemma llr_self (μ : Measure α) [SigmaFinite μ] : llr μ μ =ᵐ[μ] 0 := by
  filter_upwards [μ.rnDeriv_self] with a ha using by simp [llr, ha]

lemma exp_llr (μ ν : Measure α) [SigmaFinite μ] :
    (fun x ↦ exp (llr μ ν x))
      =ᵐ[ν] fun x ↦ if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv ν x).toReal := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [llr, h_zero, ENNReal.toReal_zero, log_zero, exp_zero, ite_true]
  · rw [llr, exp_log, if_neg h_zero]
    exact ENNReal.toReal_pos h_zero hx.ne

lemma exp_llr_of_ac (μ ν : Measure α) [SigmaFinite μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) :
    (fun x ↦ exp (llr μ ν x)) =ᵐ[μ] fun x ↦ (μ.rnDeriv ν x).toReal := by
  filter_upwards [hμν.ae_le (exp_llr μ ν), Measure.rnDeriv_pos hμν] with x hx_eq hx_pos
  rw [hx_eq, if_neg hx_pos.ne']

lemma exp_llr_of_ac' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) :
    (fun x ↦ exp (llr μ ν x)) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toReal := by
  filter_upwards [exp_llr μ ν, Measure.rnDeriv_pos' hμν] with x hx hx_pos
  rwa [if_neg hx_pos.ne'] at hx

lemma neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    -llr μ ν =ᵐ[μ] llr ν μ := by
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [Pi.neg_apply, llr, llr, ← log_inv, ← ENNReal.toReal_inv]
  congr

lemma exp_neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (fun x ↦ exp (-llr μ ν x)) =ᵐ[μ] fun x ↦ (ν.rnDeriv μ x).toReal := by
  filter_upwards [neg_llr hμν, exp_llr_of_ac' ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply] at hx
  rw [hx, hx_exp_log]

lemma exp_neg_llr' [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) :
    (fun x ↦ exp (-llr μ ν x)) =ᵐ[ν] fun x ↦ (ν.rnDeriv μ x).toReal := by
  filter_upwards [neg_llr hμν, exp_llr_of_ac ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply, neg_eq_iff_eq_neg] at hx
  rw [← hx, hx_exp_log]
