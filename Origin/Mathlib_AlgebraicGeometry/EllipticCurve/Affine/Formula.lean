/-
Extracted from AlgebraicGeometry/EllipticCurve/Affine/Formula.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Negation and addition formulae for nonsingular points in affine coordinates

Let `W` be a Weierstrass curve over a field `F` with coefficients `aᵢ`. The nonsingular affine
points on `W` can be given negation and addition operations defined by a secant-and-tangent process.
* Given a nonsingular affine point `P`, its *negation* `-P` is defined to be the unique third
  nonsingular point of intersection between `W` and the vertical line through `P`.
  Explicitly, if `P` is `(x, y)`, then `-P` is `(x, -y - a₁x - a₃)`.
* Given two nonsingular affine points `P` and `Q`, their *addition* `P + Q` is defined to be the
  negation of the unique third nonsingular point of intersection between `W` and the line `L`
  through `P` and `Q`. Explicitly, let `P` be `(x₁, y₁)` and let `Q` be `(x₂, y₂)`.
    * If `x₁ = x₂` and `y₁ = -y₂ - a₁x₂ - a₃`, then `L` is vertical.
    * If `x₁ = x₂` and `y₁ ≠ -y₂ - a₁x₂ - a₃`, then `L` is the tangent of `W` at `P = Q`, and has
      slope `ℓ := (3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (2y₁ + a₁x₁ + a₃)`.
    * Otherwise `x₁ ≠ x₂`, then `L` is the secant of `W` through `P` and `Q`, and has slope
      `ℓ := (y₁ - y₂) / (x₁ - x₂)`.

  In the last two cases, the `X`-coordinate of `P + Q` is then the unique third solution of the
  equation obtained by substituting the line `Y = ℓ(X - x₁) + y₁` into the Weierstrass equation,
  and can be written down explicitly as `x := ℓ² + a₁ℓ - a₂ - x₁ - x₂` by inspecting the
  coefficients of `X²`. The `Y`-coordinate of `P + Q`, after applying the final negation that maps
  `Y` to `-Y - a₁X - a₃`, is precisely `y := -(ℓ(x - x₁) + y₁) - a₁x - a₃`.

This file defines polynomials associated to negation and addition of nonsingular affine points,
including slopes of non-vertical lines. The actual group law on nonsingular points in affine
coordinates will be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`.

## Main definitions

* `WeierstrassCurve.Affine.negY`: the `Y`-coordinate of `-P`.
* `WeierstrassCurve.Affine.addX`: the `X`-coordinate of `P + Q`.
* `WeierstrassCurve.Affine.negAddY`: the `Y`-coordinate of `-(P + Q)`.
* `WeierstrassCurve.Affine.addY`: the `Y`-coordinate of `P + Q`.

## Main statements

* `WeierstrassCurve.Affine.equation_neg`: negation preserves the Weierstrass equation.
* `WeierstrassCurve.Affine.nonsingular_neg`: negation preserves the nonsingular condition.
* `WeierstrassCurve.Affine.equation_add`: addition preserves the Weierstrass equation.
* `WeierstrassCurve.Affine.nonsingular_add`: addition preserves the nonsingular condition.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, affine, negation, doubling, addition, group law
-/

open Polynomial

open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>

  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local macro "derivative_simp" : tactic =>

  `(tactic| simp only [derivative_C, derivative_X, derivative_X_pow, derivative_neg, derivative_add,

    derivative_sub, derivative_mul, derivative_sq])

local macro "eval_simp" : tactic =>

  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow, evalEval])

local macro "map_simp" : tactic =>

  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,

    Polynomial.map_ofNat, map_C, map_X, Polynomial.map_neg, Polynomial.map_add, Polynomial.map_sub,

    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,

    WeierstrassCurve.map])

universe r s u v w

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Affine R} {W : Affine F}

namespace Affine

/-! ## Negation formulae in affine coordinates -/

variable (W') in

noncomputable def negPolynomial : R[X][Y] :=
  -(Y : R[X][Y]) - C (C W'.a₁ * X + C W'.a₃)

lemma Y_sub_polynomialY : Y - W'.polynomialY = W'.negPolynomial := by
  rw [polynomialY, negPolynomial]
  C_simp
  ring1

lemma Y_sub_negPolynomial : Y - W'.negPolynomial = W'.polynomialY := by
  rw [← Y_sub_polynomialY, sub_sub_cancel]

variable (W') in
