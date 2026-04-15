/-
Extracted from Analysis/Calculus/FDeriv/Star.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the Fréchet derivative of the
star operation. For detailed documentation of the Fréchet derivative, see the module docstring of
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

Most of the results in this file only apply when the field that the derivative is respect to has a
trivial star operation; which as should be expected rules out `𝕜 = ℂ`. The exceptions are
`HasFDerivAt.star_star` and `DifferentiableAt.star_star`, showing that `star ∘ f ∘ star` is
differentiable when `f` is (and giving a formula for its derivative).
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [StarAddMonoid F] [NormedSpace 𝕜 F] [StarModule 𝕜 F]
  [ContinuousStar F]

variable {f : E → F} {f' : E →L[𝕜] F} {x : E} {s : Set E} {L : Filter (E × E)}

section TrivialStar

variable [TrivialStar 𝕜]

protected theorem HasFDerivAtFilter.star (h : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L f') L :=
  (starL' 𝕜 : F ≃L[𝕜] F).toContinuousLinearMap.hasFDerivAtFilter.comp h Filter.tendsto_map
