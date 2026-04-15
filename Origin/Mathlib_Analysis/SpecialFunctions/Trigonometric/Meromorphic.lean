/-
Extracted from Analysis/SpecialFunctions/Trigonometric/Meromorphic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Meromorphicity of `Complex.tan` and `Complex.tanh`
-/

namespace Complex

theorem meromorphicNFOn_tan : MeromorphicNFOn tan Set.univ := by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sin analyticAt_cos.meromorphicNFAt ?_
  grind [sin_sq_add_cos_sq]
