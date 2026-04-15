/-
Extracted from Analysis/Calculus/LogDeriv.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Logarithmic Derivatives

We define the logarithmic derivative of a function `f` as `deriv f / f`. We then prove some basic
facts about this, including how it changes under multiplication and composition.

-/

noncomputable section

open Filter Function Set

open scoped Topology

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

def logDeriv (f : 𝕜 → 𝕜') :=
  deriv f / f

lemma logDeriv_eq_zero_of_not_differentiableAt (f : 𝕜 → 𝕜') (x : 𝕜) (h : ¬DifferentiableAt 𝕜 f x) :
    logDeriv f x = 0 := by
  simp only [logDeriv_apply, deriv_zero_of_not_differentiableAt h, zero_div]
