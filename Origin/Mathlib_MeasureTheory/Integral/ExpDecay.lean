/-
Extracted from MeasureTheory/Integral/ExpDecay.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrals with exponential decay at ∞

As easy special cases of general theorems in the library, we prove the following test
for integrability:

* `integrable_of_isBigO_exp_neg`: If `f` is continuous on `[a,∞)`, for some `a ∈ ℝ`, and there
  exists `b > 0` such that `f(x) = O(exp(-b x))` as `x → ∞`, then `f` is integrable on `(a, ∞)`.
-/

noncomputable section

open Real intervalIntegral MeasureTheory Set Filter

open scoped Topology

theorem exp_neg_integrableOn_Ioi (a : ℝ) {b : ℝ} (h : 0 < b) :
    IntegrableOn (fun x : ℝ => exp (-b * x)) (Ioi a) := by
  have : Tendsto (fun x => -exp (-b * x) / b) atTop (𝓝 (-0 / b)) := by
    refine Tendsto.div_const (Tendsto.neg ?_) _
    exact tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 h))
  refine integrableOn_Ioi_deriv_of_nonneg' (fun x _ => ?_) (fun x _ => (exp_pos _).le) this
  simpa [h.ne'] using ((hasDerivAt_id x).const_mul b).neg.exp.neg.div_const b

theorem integrable_of_isBigO_exp_neg {f : ℝ → ℝ} {a b : ℝ} (h0 : 0 < b)
    (hf : ContinuousOn f (Ici a)) (ho : f =O[atTop] fun x => exp (-b * x)) :
    IntegrableOn f (Ioi a) :=
  integrableOn_Ici_iff_integrableOn_Ioi.mp <|
    (hf.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    ho ⟨Ioi b, Ioi_mem_atTop b, exp_neg_integrableOn_Ioi b h0⟩
