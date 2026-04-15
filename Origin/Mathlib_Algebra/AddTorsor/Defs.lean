/-
Extracted from Algebra/AddTorsor/Defs.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Torsors of additive group actions

This file defines torsors of additive group actions.

## Notation

The group elements are referred to as acting on points.  This file
defines the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element.

## Implementation notes

Affine spaces are the motivating example of torsors of additive group actions. It may be appropriate
to refactor in terms of the general definition of group actions, via `to_additive`, when there is a
use for multiplicative torsors (currently mathlib only develops the theory of group actions for
multiplicative group actions).

## Notation

* `v +ᵥ p` is a notation for `VAdd.vadd`, the left action of an additive monoid;

* `p₁ -ᵥ p₂` is a notation for `VSub.vsub`, difference between two points in an additive torsor
  as an element of the corresponding additive group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/

assert_not_exists MonoidWithZero

class AddTorsor (G : outParam Type*) (P : Type*) [AddGroup G] extends AddAction G P,
  VSub G P where
  [nonempty : Nonempty P]
  /-- Torsor subtraction and addition with the same element cancels out. -/
  vsub_vadd' : ∀ p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
  /-- Torsor addition and subtraction with the same element cancels out. -/
  vadd_vsub' : ∀ (g : G) (p : P), (g +ᵥ p) -ᵥ p = g

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): addGroupIsAddTorsor
