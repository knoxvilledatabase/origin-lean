/-
Extracted from Analysis/Convex/Between.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Betweenness in affine spaces

This file defines notions of a point in an affine space being between two given points.

## Main definitions

* `affineSegment R x y`: The segment of points weakly between `x` and `y`.
* `Wbtw R x y z`: The point `y` is weakly between `x` and `z`.
* `Sbtw R x y z`: The point `y` is strictly between `x` and `z`.

-/

variable (R : Type*) {V V' P P' : Type*}

open AffineEquiv AffineMap Module

section OrderedRing

def affineSegment [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V]
    [AddTorsor V P] (x y : P) :=
  lineMap x y '' Set.Icc (0 : R) 1

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

lemma affineSegment_subset_affineSpan (x y : P) : affineSegment R x y ⊆ line[R, x, y] := by
  rw [affineSegment, Set.subset_def]
  rintro p ⟨r, -, rfl⟩
  exact lineMap_mem_affineSpan_pair _ _ _

variable {R} in
