/-
Extracted from Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/ConjSqrt.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conjugating by the square root of a positive element in a C⋆-algebra

This file defines `conjSqrt c a` as `sqrt c * a * sqrt c`, and develops API for this operation.

## Main declarations

* `conjSqrt c`: the map `fun a => sqrt c * a * sqrt c`, bundled as a continuous linear map,
-/

namespace CFC

open Ring

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [SeparatelyContinuousMul A]

noncomputable def conjSqrt (c : A) : A →L[ℝ] A where
  toLinearMap := .mulLeftRight ℝ (sqrt c, sqrt c)
  cont := by
    dsimp [LinearMap.mulLeftRight, LinearMap.mulLeft, LinearMap.mulRight]
    fun_prop
