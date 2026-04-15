/-
Extracted from AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Division polynomials of Weierstrass curves

This file computes the leading terms of certain polynomials associated to division polynomials of
Weierstrass curves defined in
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`.

## Mathematical background

Let `W` be a Weierstrass curve over a commutative ring `R`. By strong induction,
* `preΨₙ` has leading coefficient `n / 2` and degree `(n² - 4) / 2` if `n` is even,
* `preΨₙ` has leading coefficient `n` and degree `(n² - 1) / 2` if `n` is odd,
* `ΨSqₙ` has leading coefficient `n²` and degree `n² - 1`, and
* `Φₙ` has leading coefficient `1` and degree `n²`.

In particular, when `R` is an integral domain of characteristic different from `n`, the univariate
polynomials `preΨₙ`, `ΨSqₙ`, and `Φₙ` all have their expected leading terms.

## Main statements

* `WeierstrassCurve.natDegree_preΨ_le`: the degree bound `d` of `preΨₙ`.
* `WeierstrassCurve.coeff_preΨ`: the `d`-th coefficient of `preΨₙ`.
* `WeierstrassCurve.natDegree_preΨ`: the degree of `preΨₙ` when `n ≠ 0`.
* `WeierstrassCurve.leadingCoeff_preΨ`: the leading coefficient of `preΨₙ` when `n ≠ 0`.
* `WeierstrassCurve.natDegree_ΨSq_le`: the degree bound `d` of `ΨSqₙ`.
* `WeierstrassCurve.coeff_ΨSq`: the `d`-th coefficient of `ΨSqₙ`.
* `WeierstrassCurve.natDegree_ΨSq`: the degree of `ΨSqₙ` when `n ≠ 0`.
* `WeierstrassCurve.leadingCoeff_ΨSq`: the leading coefficient of `ΨSqₙ` when `n ≠ 0`.
* `WeierstrassCurve.natDegree_Φ_le`: the degree bound `d` of `Φₙ`.
* `WeierstrassCurve.coeff_Φ`: the `d`-th coefficient of `Φₙ`.
* `WeierstrassCurve.natDegree_Φ`: the degree of `Φₙ` when `n ≠ 0`.
* `WeierstrassCurve.leadingCoeff_Φ`: the leading coefficient of `Φₙ` when `n ≠ 0`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

open Polynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Ψ₂Sq

lemma natDegree_Ψ₂Sq_le : W.Ψ₂Sq.natDegree ≤ 3 := by
  rw [Ψ₂Sq]
  compute_degree
