/-
Extracted from Analysis/SpecialFunctions/Pow/NNReal.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

public meta import Mathlib.Data.Nat.NthRoot.Defs

/-!
# Power function on `ℝ≥0` and `ℝ≥0∞`

We construct the power functions `x ^ y` where
* `x` is a nonnegative real number and `y` is a real number;
* `x` is a number from `[0, +∞]` (a.k.a. `ℝ≥0∞`) and `y` is a real number.

We also prove basic properties of these functions.
-/

noncomputable section

open Real NNReal ENNReal ComplexConjugate Finset Function Set

namespace NNReal

variable {x : ℝ≥0} {w y z : ℝ}

noncomputable def rpow (x : ℝ≥0) (y : ℝ) : ℝ≥0 :=
  ⟨(x : ℝ) ^ y, Real.rpow_nonneg x.2 y⟩

-- INSTANCE (free from Core): :
