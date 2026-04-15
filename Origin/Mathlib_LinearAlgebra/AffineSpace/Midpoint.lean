/-
Extracted from LinearAlgebra/AffineSpace/Midpoint.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Midpoint of a segment

## Main definitions

* `midpoint R x y`: midpoint of the segment `[x, y]`. We define it for `x` and `y`
  in a module over a ring `R` with invertible `2`.
* `AddMonoidHom.ofMapMidpoint`: construct an `AddMonoidHom` given a map `f` such that
  `f` sends zero to zero and midpoints to midpoints.

## Main theorems

* `midpoint_eq_iff`: `z` is the midpoint of `[x, y]` if and only if `x + y = z + z`,
* `midpoint_unique`: `midpoint R x y` does not depend on `R`;
* `midpoint x y` is linear both in `x` and `y`;
* `pointReflection_midpoint_left`, `pointReflection_midpoint_right`:
  `Equiv.pointReflection (midpoint R x y)` swaps `x` and `y`.

We do not mark most lemmas as `@[simp]` because it is hard to tell which side is simpler.

## Tags

midpoint, AddMonoidHom
-/

open AffineMap AffineEquiv

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

def midpoint (x y : P) : P :=
  lineMap x y (⅟2 : R)

variable {R} {x y z : P}
