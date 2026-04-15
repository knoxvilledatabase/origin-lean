/-
Extracted from LinearAlgebra/AffineSpace/Combination.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Affine combinations of points

This file defines affine combinations of points.

## Main definitions

* `weightedVSubOfPoint` is a general weighted combination of
  subtractions with an explicit base point, yielding a vector.

* `weightedVSub` uses an arbitrary choice of base point and is intended
  to be used when the sum of weights is 0, in which case the result is
  independent of the choice of base point.

* `affineCombination` adds the weighted combination to the arbitrary
  base point, yielding a point rather than a vector, and is intended
  to be used when the sum of weights is 1, in which case the result is
  independent of the choice of base point.

These definitions are for sums over a `Finset`; versions for a
`Fintype` may be obtained using `Finset.univ`, while versions for a
`Finsupp` may be obtained using `Finsupp.support`.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

noncomputable section

open Affine

namespace Finset

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AffineSpace V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

def weightedVSubOfPoint (p : ι → P) (b : P) : (ι → k) →ₗ[k] V :=
  ∑ i ∈ s, (LinearMap.proj i : (ι → k) →ₗ[k] k).smulRight (p i -ᵥ b)
