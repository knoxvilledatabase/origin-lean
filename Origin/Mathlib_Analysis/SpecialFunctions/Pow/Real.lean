/-
Extracted from Analysis/SpecialFunctions/Pow/Real.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

public meta import Mathlib.Data.Nat.NthRoot.Defs

/-! # Power function on `ℝ`

We construct the power functions `x ^ y`, where `x` and `y` are real numbers.
-/

noncomputable section

open Real ComplexConjugate Finset Set

namespace Real

variable {x y z : ℝ}

noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re

-- INSTANCE (free from Core): :
