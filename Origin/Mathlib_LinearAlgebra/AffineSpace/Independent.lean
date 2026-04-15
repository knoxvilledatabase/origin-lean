/-
Extracted from LinearAlgebra/AffineSpace/Independent.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Affine independence

This file defines affinely independent families of points.

## Main definitions

* `AffineIndependent` defines affinely independent families of points
  as those where no nontrivial weighted subtraction is `0`.  This is
  proved equivalent to two other formulations: linear independence of
  the results of subtracting a base point in the family from the other
  points in the family, or any equal affine combinations having the
  same weights.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

noncomputable section

open Finset Function Module

open scoped Affine

section AffineIndependent

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AffineSpace V P] {ι : Type*}

def AffineIndependent (p : ι → P) : Prop :=
  ∀ (s : Finset ι) (w : ι → k),
    ∑ i ∈ s, w i = 0 → s.weightedVSub p w = (0 : V) → ∀ i ∈ s, w i = 0

theorem affineIndependent_of_subsingleton [Subsingleton ι] (p : ι → P) : AffineIndependent k p :=
  fun _ _ h _ i hi => Fintype.eq_of_subsingleton_of_sum_eq h i hi
