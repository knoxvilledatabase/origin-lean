/-
Extracted from Analysis/SpecialFunctions/Trigonometric/Angle.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The type of angles

In this file we define `Real.Angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/

open Real

noncomputable section

namespace Real

def Angle : Type :=
  AddCircle (2 * π)

deriving NormedAddCommGroup, Inhabited

namespace Angle
