/-
Extracted from Analysis/SpecialFunctions/Sqrt.lean
Genuine: 1 | Conflates: 0 | Dissolved: 22 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Smoothness of `Real.sqrt`

In this file we prove that `Real.sqrt` is infinitely smooth at all points `x ≠ 0` and provide some
dot-notation lemmas.

## Tags

sqrt, differentiable
-/

open Set

open scoped Topology

namespace Real

noncomputable def sqPartialHomeomorph : PartialHomeomorph ℝ ℝ where
  toFun x := x ^ 2
  invFun := (√·)
  source := Ioi 0
  target := Ioi 0
  map_source' _ h := mem_Ioi.2 (pow_pos (mem_Ioi.1 h) _)
  map_target' _ h := mem_Ioi.2 (sqrt_pos.2 h)
  left_inv' _ h := sqrt_sq (le_of_lt h)
  right_inv' _ h := sq_sqrt (le_of_lt h)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
  continuousOn_toFun := (continuous_pow 2).continuousOn
  continuousOn_invFun := continuousOn_id.sqrt

-- DISSOLVED: deriv_sqrt_aux

-- DISSOLVED: hasStrictDerivAt_sqrt

-- DISSOLVED: contDiffAt_sqrt

-- DISSOLVED: hasDerivAt_sqrt

end Real

open Real

section deriv

variable {f : ℝ → ℝ} {s : Set ℝ} {f' x : ℝ}

-- DISSOLVED: HasDerivWithinAt.sqrt

-- DISSOLVED: HasDerivAt.sqrt

-- DISSOLVED: HasStrictDerivAt.sqrt

-- DISSOLVED: derivWithin_sqrt

-- DISSOLVED: deriv_sqrt

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {n : WithTop ℕ∞}
  {s : Set E} {x : E} {f' : E →L[ℝ] ℝ}

-- DISSOLVED: HasFDerivAt.sqrt

-- DISSOLVED: HasStrictFDerivAt.sqrt

-- DISSOLVED: HasFDerivWithinAt.sqrt

-- DISSOLVED: DifferentiableWithinAt.sqrt

-- DISSOLVED: DifferentiableAt.sqrt

-- DISSOLVED: DifferentiableOn.sqrt

-- DISSOLVED: Differentiable.sqrt

-- DISSOLVED: fderivWithin_sqrt

-- DISSOLVED: fderiv_sqrt

-- DISSOLVED: ContDiffAt.sqrt

-- DISSOLVED: ContDiffWithinAt.sqrt

-- DISSOLVED: ContDiffOn.sqrt

-- DISSOLVED: ContDiff.sqrt

end fderiv
