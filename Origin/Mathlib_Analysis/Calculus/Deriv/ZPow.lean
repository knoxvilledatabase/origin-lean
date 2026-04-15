/-
Extracted from Analysis/Calculus/Deriv/ZPow.lean
Genuine: 2 of 7 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivatives of `x ^ m`, `m : ℤ`

In this file we prove theorems about (iterated) derivatives of `x ^ m`, `m : ℤ`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, power
-/

universe u v w

open Topology Filter Asymptotics Set

open scoped Nat

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {x : 𝕜}

variable {s : Set 𝕜}

variable {m : ℤ}

/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/

-- DISSOLVED: hasStrictDerivAt_zpow

-- DISSOLVED: hasDerivAt_zpow

-- DISSOLVED: hasDerivWithinAt_zpow

-- DISSOLVED: differentiableAt_zpow

-- DISSOLVED: differentiableWithinAt_zpow

theorem differentiableOn_zpow (m : ℤ) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 ≤ m) :
    DifferentiableOn 𝕜 (fun x => x ^ m) s := fun x hxs =>
  differentiableWithinAt_zpow m x <| h.imp_left <| ne_of_mem_of_not_mem hxs

theorem deriv_zpow (m : ℤ) (x : 𝕜) : deriv (fun x => x ^ m) x = m * x ^ (m - 1) := by
  by_cases H : x ≠ 0 ∨ 0 ≤ m
  · exact (hasDerivAt_zpow m x H).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_zpow.1 H)]
    push Not at H
    rcases H with ⟨rfl, hm⟩
    rw [zero_zpow _ ((sub_one_lt _).trans hm).ne, mul_zero]
