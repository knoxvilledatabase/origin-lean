/-
Extracted from Analysis/Calculus/Deriv/Star.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the derivative of the star
operation.

Most of the results in this file only apply when the field that the derivative is respect to has a
trivial star operation; which as should be expected rules out `𝕜 = ℂ`. The exceptions are
`HasDerivAt.conj_conj` and `DifferentiableAt.conj_conj`, showing that `conj ∘ f ∘ conj` is
differentiable when `f` is (and giving a formula for its derivative).
-/

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [StarAddMonoid F] [StarModule 𝕜 F]
  [ContinuousStar F] {f : 𝕜 → F} {f' : F} {x : 𝕜}

/-! ### Derivative of `x ↦ star x` -/

section TrivialStar

variable [TrivialStar 𝕜] {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}

protected theorem HasDerivAtFilter.star (h : HasDerivAtFilter f f' L) :
    HasDerivAtFilter (fun x => star (f x)) (star f') L := by
  simpa using h.hasFDerivAtFilter.star.hasDerivAtFilter

protected theorem HasDerivWithinAt.star (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => star (f x)) (star f') s x :=
  HasDerivAtFilter.star h

protected theorem HasDerivAt.star (h : HasDerivAt f f' x) :
    HasDerivAt (fun x => star (f x)) (star f') x :=
  HasDerivAtFilter.star h

protected nonrec theorem HasStrictDerivAt.star (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => star (f x)) (star f') x :=
  HasDerivAtFilter.star h

protected theorem derivWithin.star :
    derivWithin (fun y => star (f y)) s x = star (derivWithin f s x) := by
  by_cases hxs : UniqueDiffWithinAt 𝕜 s x
  · exact DFunLike.congr_fun (fderivWithin_star hxs) _
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hxs]

protected theorem deriv.star : deriv (fun y => star (f y)) x = star (deriv f x) :=
  DFunLike.congr_fun fderiv_star _
