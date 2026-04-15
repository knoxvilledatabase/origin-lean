/-
Extracted from Analysis/Distribution/SchwartzSpace/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Schwartz space

This file defines the Schwartz space. Usually, the Schwartz space is defined as the set of smooth
functions $f : ℝ^n → ℂ$ such that there exists $C_{αβ} > 0$ with $$|x^α ∂^β f(x)| < C_{αβ}$$ for
all $x ∈ ℝ^n$ and for all multiindices $α, β$.
In mathlib, we use a slightly different approach and define the Schwartz space as all
smooth functions `f : E → F`, where `E` and `F` are real normed vector spaces such that for all
natural numbers `k` and `n` we have uniform bounds `‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ < C`.
This approach completely avoids using partial derivatives as well as polynomials.
We construct the topology on the Schwartz space by a family of seminorms, which are the best
constants in the above estimates. The abstract theory of topological vector spaces developed in
`SeminormFamily.moduleFilterBasis` and `WithSeminorms.toLocallyConvexSpace` turns the
Schwartz space into a locally convex topological vector space.

## Main definitions

* `SchwartzMap`: The Schwartz space is the space of smooth functions such that all derivatives
  decay faster than any power of `‖x‖`.
* `SchwartzMap.seminorm`: The family of seminorms as described above
* `SchwartzMap.compCLM`: Composition with a function on the right as a continuous linear map
  `𝓢(E, F) →L[𝕜] 𝓢(D, F)`, provided that the function is temperate and grows polynomially near
  infinity
* `SchwartzMap.integralCLM`: Integration as a continuous linear map `𝓢(ℝ, F) →L[ℝ] F`

## Main statements

* `SchwartzMap.instIsUniformAddGroup` and `SchwartzMap.instLocallyConvexSpace`: The Schwartz space
  is a locally convex topological vector space.
* `SchwartzMap.one_add_le_sup_seminorm_apply`: For a Schwartz function `f` there is a uniform bound
  on `(1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖`.

## Implementation details

The implementation of the seminorms is taken almost literally from `ContinuousLinearMap.opNorm`.

## Notation

* `𝓢(E, F)`: The Schwartz space `SchwartzMap E F` localized in `SchwartzSpace`

## Tags

Schwartz space, tempered distributions
-/

open scoped Nat NNReal ContDiff

variable {ι 𝕜 𝕜' D E F G H V : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E F) in

structure SchwartzMap where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : E → F
  smooth' : ContDiff ℝ ∞ toFun
  decay' : ∀ k n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n toFun x‖ ≤ C

scoped[SchwartzMap] notation "𝓢(" E ", " F ")" => SchwartzMap E F

namespace SchwartzMap

-- INSTANCE (free from Core): instFunLike

theorem decay (f : 𝓢(E, F)) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  rcases f.decay' k n with ⟨C, hC⟩
  exact ⟨max C 1, by positivity, fun x => (hC x).trans (le_max_left _ _)⟩
