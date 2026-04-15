/-
Extracted from LinearAlgebra/AffineSpace/Centroid.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Centroid of a Finite Set of Points in Affine Space

This file defines the centroid of a finite set of points in an affine space over a division
ring.

## Main definitions

* `centroidWeights`: A constant weight function assigning to each index in a `Finset` the same
  weight, equal to the reciprocal of the number of elements.

* `centroid`: the centroid of a `Finset` of points, defined as the affine combination using
  `centroidWeights`.

-/

assert_not_exists Affine.Simplex

noncomputable section

open Affine

namespace Finset

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AffineSpace V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

def centroidWeights : ι → k :=
  Function.const ι (#s : k)⁻¹
