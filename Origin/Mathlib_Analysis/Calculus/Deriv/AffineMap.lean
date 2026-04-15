/-
Extracted from Analysis/Calculus/Deriv/AffineMap.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivatives of affine maps

In this file we prove formulas for one-dimensional derivatives of affine maps `f : 𝕜 →ᵃ[𝕜] E`. We
also specialise some of these results to `AffineMap.lineMap` because it is useful to transfer MVT
from dimension 1 to a domain in higher dimension.

## TODO

Add theorems about `deriv`s and `fderiv`s of `ContinuousAffineMap`s once they will be ported to
Mathlib 4.

## Keywords

affine map, derivative, differentiability
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (f : 𝕜 →ᵃ[𝕜] E) {a b : E} {L : Filter (𝕜 × 𝕜)} {s : Set 𝕜} {x : 𝕜}

namespace AffineMap

theorem hasDerivAtFilter : HasDerivAtFilter f (f.linear 1) L := by
  rw [f.decomp]
  exact f.linear.hasDerivAtFilter.add_const (f 0)

theorem hasStrictDerivAt : HasStrictDerivAt f (f.linear 1) x := f.hasDerivAtFilter

theorem hasDerivWithinAt : HasDerivWithinAt f (f.linear 1) s x := f.hasDerivAtFilter

theorem hasDerivAt : HasDerivAt f (f.linear 1) x := f.hasDerivAtFilter

protected theorem derivWithin (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = f.linear 1 :=
  f.hasDerivWithinAt.derivWithin hs
