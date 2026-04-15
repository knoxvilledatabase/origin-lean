/-
Extracted from Analysis/Calculus/Gradient/Basic.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gradient

## Main Definitions

Let `f` be a function from a Hilbert Space `F` to `𝕜` (`𝕜` is `ℝ` or `ℂ`), `x` be a point in `F`
and `f'` be a vector in F. Then

  `HasGradientWithinAt f f' s x`

says that `f` has a gradient `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasGradientAt f f' x := HasGradientWithinAt f f' x univ`

## Main results

This file develops the following aspects of the theory of gradients:
* definitions of gradients, both within a set and on the whole space.
* translating between `HasGradientAtFilter` and `HasFDerivAtFilter`,
  `HasGradientWithinAt` and `HasFDerivWithinAt`, `HasGradientAt` and `HasFDerivAt`,
  `gradient` and `fderiv`.
* uniqueness of gradients.
* translating between `HasGradientAtFilter` and `HasDerivAtFilter`,
  `HasGradientAt` and `HasDerivAt`, `gradient` and `deriv` when `F = 𝕜`.
* the theorems about the inner product of the gradient.
* the congruence of the gradient.
* the gradient of constant functions.
* the continuity of a function admitting a gradient.
-/

open ComplexConjugate Topology InnerProductSpace Function Set

noncomputable section

variable {𝕜 F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

variable {f : F → 𝕜} {f' x y : F}

def HasGradientAtFilter (f : F → 𝕜) (f' x : F) (L : Filter F) :=
  HasFDerivAtFilter f (toDual 𝕜 F f') (L ×ˢ pure x)

def HasGradientWithinAt (f : F → 𝕜) (f' : F) (s : Set F) (x : F) :=
  HasGradientAtFilter f f' x (𝓝[s] x)

def HasGradientAt (f : F → 𝕜) (f' x : F) :=
  HasGradientAtFilter f f' x (𝓝 x)

def gradientWithin (f : F → 𝕜) (s : Set F) (x : F) : F :=
  (toDual 𝕜 F).symm (fderivWithin 𝕜 f s x)

def gradient (f : F → 𝕜) (x : F) : F :=
  (toDual 𝕜 F).symm (fderiv 𝕜 f x)
