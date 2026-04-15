/-
Extracted from Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Representation of `log⁺` as a Circle Average

If `a` is any complex number, `circleAverage_log_norm_sub_const_eq_posLog` represents `log⁺ a` as
the circle average of `log ‖· - a‖` over the unit circle.
-/

open Filter Interval intervalIntegral MeasureTheory Metric Real

variable {a c : ℂ} {R : ℝ}

/-!
## Circle Integrability
-/

lemma circleIntegrable_log_norm_sub_const (r : ℝ) : CircleIntegrable (log ‖· - a‖) c r :=
  MeromorphicOn.circleIntegrable_log_norm (fun z hz ↦ by fun_prop)

/-!
## Computing `circleAverage (log ‖· - a‖) 0 1` in case where `‖a‖ < 1`.
-/
