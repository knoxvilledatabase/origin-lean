/-
Extracted from Analysis/Convex/Combination.lean
Genuine: 3 of 5 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Convex combinations

This file defines convex combinations of points in a vector space.

## Main declarations

* `Finset.centerMass`: Center of mass of a finite family of points.

## Implementation notes

We divide by the sum of the weights in the definition of `Finset.centerMass` because of the way
mathematical arguments go: one doesn't change weights, but merely adds some. This also makes a few
lemmas unconditional on the sum of the weights being `1`.
-/

assert_not_exists Cardinal

open Set Function Pointwise

universe u u'

variable {R R' E F ι ι' α : Type*} [Field R] [Field R'] [AddCommGroup E] [AddCommGroup F]
  [AddCommGroup α] [LinearOrder α] [Module R E] [Module R F] [Module R α] {s : Set E}

def Finset.centerMass (t : Finset ι) (w : ι → R) (z : ι → E) : E :=
  (∑ i ∈ t, w i)⁻¹ • ∑ i ∈ t, w i • z i

variable (i j : ι) (c : R) (t : Finset ι) (w : ι → R) (z : ι → E)

open Finset

theorem Finset.centerMass_empty : (∅ : Finset ι).centerMass w z = 0 := by
  simp only [centerMass, sum_empty, smul_zero]

theorem Finset.centerMass_pair [DecidableEq ι] (hne : i ≠ j) :
    ({i, j} : Finset ι).centerMass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j := by
  simp only [centerMass, sum_pair hne]
  module

variable {w}

-- DISSOLVED: Finset.centerMass_insert

-- DISSOLVED: Finset.centerMass_singleton
