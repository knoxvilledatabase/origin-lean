/-
Extracted from Analysis/SpecialFunctions/Complex/CircleMap.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# circleMap

This file defines the circle map $θ ↦ c + R e^{θi}$, a parametrization of a circle.

## Main definitions

* `circleMap c R`: the exponential map $θ ↦ c + R e^{θi}$.

## Tags

-/

noncomputable section circleMap

open Complex Function Metric Real

def circleMap (c : ℂ) (R : ℝ) : ℝ → ℂ := fun θ => c + R * exp (θ * I)
