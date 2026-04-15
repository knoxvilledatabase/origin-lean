/-
Extracted from Analysis/Calculus/IteratedDeriv/ConvergenceOnBall.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Taylor series converges to function on whole ball

In this file we prove that if a function `f` is analytic on the ball of convergence of its Taylor
series, then the series converges to `f` on this ball.
-/

variable {𝕜 : Type*} [RCLike 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜}

theorem AnalyticOn.hasFPowerSeriesOnBall :
    letI p := FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n f x / n.factorial);
    0 < p.radius → AnalyticOn 𝕜 f (Metric.eball x p.radius) →
    HasFPowerSeriesOnBall f p x p.radius := by
  intro hr hs
  exact hs.hasFPowerSeriesOnSubball hr le_rfl
