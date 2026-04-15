/-
Extracted from Combinatorics/Quiver/Path/Weight.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Path weights in a Quiver

This file defines the weight of a path in a quiver. The weight of a path is the product of the
weights of its edges, where weights are taken from a monoid.

## Main definitions

* `Quiver.Path.weight`: The weight of a path, defined as the multiplicative product of the
  weights of its constituent edges.
* `Quiver.Path.weightOfEPs`: A convenience version of `weight` where the weight of an edge
  is determined by a function of its source and target vertices.

## Main results

* `Quiver.Path.weight_comp`: The weight of a composition of paths is the product of their weights.
* `Quiver.Path.weight_pos`: If all edge weights are positive, the path weight is positive.
* `Quiver.Path.weightOfEPs_nonneg`: If all edge weights are non-negative, so is the path weight.
-/

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*}

section Weight

variable [Monoid R]

def weight (w : ∀ {i j : V}, (i ⟶ j) → R) : ∀ {i j : V}, Path i j → R
  | _, _, Path.nil => 1
  | _, _, Path.cons p e => weight w p * w e

def addWeight {R : Type*} [AddMonoid R] (w : ∀ {i j : V}, (i ⟶ j) → R) : ∀ {i j : V}, Path i j → R
  | _, _, Path.nil => 0
  | _, _, Path.cons p e => addWeight w p + w e

attribute [to_additive existing addWeight] weight
