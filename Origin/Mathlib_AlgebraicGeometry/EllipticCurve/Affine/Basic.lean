/-
Extracted from AlgebraicGeometry/EllipticCurve/Affine/Basic.lean
Genuine: 4 of 5 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Weierstrass equations and the nonsingular condition in affine coordinates

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. An *affine point*
on `W` is a tuple `(x, y)` of elements in `R` satisfying the *Weierstrass equation* `W(X, Y) = 0` in
*affine coordinates*, where `W(X, Y) := Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)`. It is
*nonsingular* if its partial derivatives `W_X(x, y)` and `W_Y(x, y)` do not vanish simultaneously.

This file defines polynomials associated to Weierstrass equations and the nonsingular condition in
affine coordinates. The group law on the actual type of nonsingular points in affine coordinates
will be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, based on the
formulae for group operations in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`.

## Main definitions

* `WeierstrassCurve.Affine.Equation`: the Weierstrass equation in affine coordinates.
* `WeierstrassCurve.Affine.Nonsingular`: the nonsingular condition in affine coordinates.

## Main statements

* `WeierstrassCurve.Affine.equation_iff_nonsingular`: an elliptic curve in affine coordinates is
  nonsingular at every point.

## Implementation notes

All definitions and lemmas for Weierstrass curves in affine coordinates live in the namespace
`WeierstrassCurve.Affine` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toAffine`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, affine, Weierstrass equation, nonsingular
-/

open Polynomial

open scoped Polynomial.Bivariate

local macro "eval_simp" : tactic =>

  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow, evalEval])

local macro "map_simp" : tactic =>

  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,

    Polynomial.map_ofNat, map_C, map_X, Polynomial.map_neg, Polynomial.map_add, Polynomial.map_sub,

    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,

    WeierstrassCurve.map])

universe r s u v

variable {R : Type r} {S : Type s} {A : Type u} {B : Type v}

namespace WeierstrassCurve

/-! ## Affine coordinates -/

variable (R) in

abbrev Affine : Type r :=
  WeierstrassCurve R

abbrev toAffine (W : WeierstrassCurve R) : Affine R :=
  W

variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] {W : Affine R}

namespace Affine

/-! ## Weierstrass equations in affine coordinates -/

variable (W) in

noncomputable def polynomial : R[X][Y] :=
  Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)

lemma polynomial_eq : W.polynomial = Cubic.toPoly
    ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩ := by
  simp_rw [polynomial, Cubic.toPoly]
  map_simp
  simp only [C_0, C_1]
  ring1

-- DISSOLVED: polynomial_ne_zero
