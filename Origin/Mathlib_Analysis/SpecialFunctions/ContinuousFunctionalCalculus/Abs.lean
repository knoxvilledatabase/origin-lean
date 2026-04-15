/-
Extracted from Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Absolute value defined via the continuous functional calculus

This file defines the absolute value via the non-unital continuous functional calculus
and provides basic API.

## Main declarations

+ `CFC.abs`: The absolute value as `abs a := CFC.sqrt (star a * a)`.

-/

variable {𝕜 A : Type*}

open scoped NNReal

open CFC

namespace CFC

section NonUnital

section Real

variable [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

noncomputable def abs (a : A) := sqrt (star a * a)
