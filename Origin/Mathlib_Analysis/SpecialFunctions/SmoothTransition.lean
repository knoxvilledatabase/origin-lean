/-
Extracted from Analysis/SpecialFunctions/SmoothTransition.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Infinitely smooth transition function

In this file we construct two infinitely smooth functions with properties that an analytic function
cannot have:

* `expNegInvGlue` is equal to zero for `x ≤ 0` and is strictly positive otherwise; it is given by
  `x ↦ exp (-1/x)` for `x > 0`;

* `Real.smoothTransition` is equal to zero for `x ≤ 0` and is equal to one for `x ≥ 1`; it is given
  by `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`;
-/

noncomputable section

open scoped Topology

open Polynomial Real Filter Set Function

def expNegInvGlue (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else exp (-x⁻¹)

namespace expNegInvGlue

theorem zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : expNegInvGlue x = 0 := by simp [expNegInvGlue, hx]
