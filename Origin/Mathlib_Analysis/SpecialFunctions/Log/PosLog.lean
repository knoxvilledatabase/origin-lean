/-
Extracted from Analysis/SpecialFunctions/Log/PosLog.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The Positive Part of the Logarithm

This file defines the function `Real.posLog = r ↦ max 0 (log r)` and introduces the notation
`log⁺`. For a finite length-`n` sequence `f i` of reals, it establishes the following standard
estimates.

- `theorem posLog_prod : log⁺ (∏ i, f i) ≤ ∑ i, log⁺ (f i)`

- `theorem posLog_sum : log⁺ (∑ i, f i) ≤ log n + ∑ i, log⁺ (f i)`

See `Mathlib/Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean` for the presentation of
`log⁺` as a Circle Average.
-/

namespace Real

variable {x y : ℝ}

/-!
## Definition, Notation and Reformulations
-/

noncomputable def posLog : ℝ → ℝ := fun r ↦ max 0 (log r)

scoped notation "log⁺" => posLog

/-!
## Elementary Properties
-/

theorem posLog_sub_posLog_inv : log⁺ x - log⁺ x⁻¹ = log x := by
  rw [posLog_def, posLog_def, log_inv]
  by_cases! h : 0 ≤ log x
  · simp [h]
  · simp [neg_nonneg.1 (Left.nonneg_neg_iff.2 h.le)]

theorem half_mul_log_add_log_abs : 2⁻¹ * (log x + |log x|) = log⁺ x := by
  by_cases! hr : 0 ≤ log x
  · simp [posLog, hr, abs_of_nonneg]
    ring
  · simp [posLog, hr.le, abs_of_nonpos]
