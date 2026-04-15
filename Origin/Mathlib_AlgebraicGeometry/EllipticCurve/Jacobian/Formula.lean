/-
Extracted from AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean
Genuine: 63 of 110 | Dissolved: 40 | Infrastructure: 7
-/
import Origin.Core

/-!
# Negation and addition formulae for nonsingular points in Jacobian coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular Jacobian points on `W` can be given
negation and addition operations defined by an analogue of the secant-and-tangent process in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`, but the polynomials involved are
`(2, 3, 1)`-homogeneous, so any instances of division become multiplication in the `Z`-coordinate.
Most computational proofs are immediate from their analogous proofs for affine coordinates.

This file defines polynomials associated to negation, doubling, and addition of Jacobian point
representatives. The group operations and the group law on actual nonsingular Jacobian points will
be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`.

## Main definitions

* `WeierstrassCurve.Jacobian.negY`: the `Y`-coordinate of `-P`.
* `WeierstrassCurve.Jacobian.dblZ`: the `Z`-coordinate of `2 • P`.
* `WeierstrassCurve.Jacobian.dblX`: the `X`-coordinate of `2 • P`.
* `WeierstrassCurve.Jacobian.negDblY`: the `Y`-coordinate of `-(2 • P)`.
* `WeierstrassCurve.Jacobian.dblY`: the `Y`-coordinate of `2 • P`.
* `WeierstrassCurve.Jacobian.addZ`: the `Z`-coordinate of `P + Q`.
* `WeierstrassCurve.Jacobian.addX`: the `X`-coordinate of `P + Q`.
* `WeierstrassCurve.Jacobian.negAddY`: the `Y`-coordinate of `-(P + Q)`.
* `WeierstrassCurve.Jacobian.addY`: the `Y`-coordinate of `P + Q`.

## Implementation notes

The definitions of `WeierstrassCurve.Jacobian.addX` and `WeierstrassCurve.Jacobian.negAddY` are
given explicitly by large polynomials that are homogeneous of degrees `8` and `12` respectively.
Clearing the denominators of their corresponding affine rational functions in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean` would give polynomials that are
homogeneous of degrees `12` and `18` respectively, so their actual definitions are off by powers of
a certain polynomial factor that is homogeneous of degree `2`. This factor divides their
corresponding affine polynomials only modulo the `(2, 3, 1)`-homogeneous Weierstrass equation, so
their large quotient polynomials are calculated explicitly in a computer algebra system. All of this
is done to ensure that the definitions of both `WeierstrassCurve.Jacobian.dblXYZ` and
`WeierstrassCurve.Jacobian.addXYZ` are `(2, 3, 1)`-homogeneous of degree `4`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, negation, doubling, addition, group law
-/

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "map_simp" : tactic =>

  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,

    map_div₀, WeierstrassCurve.map, Function.comp_apply])

universe r s u v

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Jacobian R} {W : Jacobian F}

namespace Jacobian

/-! ## Negation formulae in Jacobian coordinates -/

variable (W') in

def negY (P : Fin 3 → R) : R :=
  -P y - W'.a₁ * P x * P z - W'.a₃ * P z ^ 3

lemma negY_smul (P : Fin 3 → R) (u : R) : W'.negY (u • P) = u ^ 3 * W'.negY P := by
  simp only [negY, smul_fin3_ext]
  ring1

lemma negY_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.negY P = -P y := by
  rw [negY, hPz, mul_zero, sub_zero, zero_pow three_ne_zero, mul_zero, sub_zero]

-- DISSOLVED: negY_of_Z_ne_zero

lemma Y_sub_Y_mul_Y_sub_negY {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    (P y * Q z ^ 3 - Q y * P z ^ 3) * (P y * Q z ^ 3 - W'.negY Q * P z ^ 3) = 0 := by
  linear_combination (norm := (rw [negY]; ring1)) Q z ^ 6 * (equation_iff P).mp hP
    - P z ^ 6 * (equation_iff Q).mp hQ + (P x ^ 2 * Q z ^ 4 + P x * Q x * P z ^ 2 * Q z ^ 2
      + Q x ^ 2 * P z ^ 4 - W'.a₁ * P y * P z * Q z ^ 4 + W'.a₂ * P x * P z ^ 2 * Q z ^ 4
      + W'.a₂ * Q x * P z ^ 4 * Q z ^ 2 + W'.a₄ * P z ^ 4 * Q z ^ 4) * hx

lemma Y_eq_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    P y * Q z ^ 3 = W'.negY Q * P z ^ 3 :=
  sub_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left <|
    sub_ne_zero.mpr hy

lemma Y_eq_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W'.negY Q * P z ^ 3) :
    P y * Q z ^ 3 = Q y * P z ^ 3 :=
  sub_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_right <|
    sub_ne_zero.mpr hy

-- DISSOLVED: Y_eq_iff'

lemma Y_sub_Y_add_Y_sub_negY {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    (P y * Q z ^ 3 - Q y * P z ^ 3) + (P y * Q z ^ 3 - W'.negY Q * P z ^ 3) =
      (P y - W'.negY P) * Q z ^ 3 := by
  linear_combination (norm := (rw [negY, negY]; ring1)) -W'.a₁ * P z * Q z * hx

lemma Y_ne_negY_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    P y ≠ W'.negY P := by
  have hy' : P y * Q z ^ 3 - W'.negY Q * P z ^ 3 = 0 :=
    (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left <| sub_ne_zero_of_ne hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z ^ 3 * hy - hy'

lemma Y_ne_negY_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ W'.negY Q * P z ^ 3) : P y ≠ W'.negY P := by
  have hy' : P y * Q z ^ 3 - Q y * P z ^ 3 = 0 :=
    (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_right <| sub_ne_zero_of_ne hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z ^ 3 * hy - hy'

-- DISSOLVED: Y_eq_negY_of_Y_eq

-- DISSOLVED: nonsingular_iff_of_Y_eq_negY

/-! ## Doubling formulae in Jacobian coordinates -/

variable (W') in

noncomputable def dblU (P : Fin 3 → R) : R :=
  eval P W'.polynomialX

lemma dblU_eq (P : Fin 3 → R) : W'.dblU P =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) := by
  rw [dblU, eval_polynomialX]

lemma dblU_smul (P : Fin 3 → R) (u : R) : W'.dblU (u • P) = u ^ 4 * W'.dblU P := by
  simp only [dblU_eq, smul_fin3_ext]
  ring1

lemma dblU_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.dblU P = -3 * P x ^ 2 := by
  rw [dblU_eq, hPz]
  ring1

-- DISSOLVED: dblU_ne_zero_of_Y_eq

-- DISSOLVED: isUnit_dblU_of_Y_eq

variable (W') in

def dblZ (P : Fin 3 → R) : R :=
  P z * (P y - W'.negY P)

lemma dblZ_smul (P : Fin 3 → R) (u : R) : W'.dblZ (u • P) = u ^ 4 * W'.dblZ P := by
  simp only [dblZ, negY_smul, smul_fin3_ext]
  ring1

lemma dblZ_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.dblZ P = 0 := by
  rw [dblZ, hPz, zero_mul]

-- DISSOLVED: dblZ_of_Y_eq

-- DISSOLVED: dblZ_ne_zero_of_Y_ne

-- DISSOLVED: isUnit_dblZ_of_Y_ne

-- DISSOLVED: dblZ_ne_zero_of_Y_ne'

-- DISSOLVED: isUnit_dblZ_of_Y_ne'

-- DISSOLVED: toAffine_slope_of_eq

variable (W') in

noncomputable def dblX (P : Fin 3 → R) : R :=
  W'.dblU P ^ 2 - W'.a₁ * W'.dblU P * P z * (P y - W'.negY P)
    - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * (P y - W'.negY P) ^ 2

lemma dblX_smul (P : Fin 3 → R) (u : R) : W'.dblX (u • P) = (u ^ 4) ^ 2 * W'.dblX P := by
  simp only [dblX, dblU_smul, negY_smul, smul_fin3_ext]
  ring1

lemma dblX_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblX P = (P x ^ 2) ^ 2 := by
  linear_combination (norm := (rw [dblX, dblU_of_Z_eq_zero hPz, negY_of_Z_eq_zero hPz, hPz]; ring1))
    -8 * P x * (equation_of_Z_eq_zero hPz).mp hP

-- DISSOLVED: dblX_of_Y_eq

set_option linter.flexible false in

-- DISSOLVED: toAffine_addX_of_eq

-- DISSOLVED: dblX_of_Z_ne_zero

variable (W') in

noncomputable def negDblY (P : Fin 3 → R) : R :=
  -W'.dblU P * (W'.dblX P - P x * (P y - W'.negY P) ^ 2) + P y * (P y - W'.negY P) ^ 3

lemma negDblY_smul (P : Fin 3 → R) (u : R) : W'.negDblY (u • P) = (u ^ 4) ^ 3 * W'.negDblY P := by
  simp only [negDblY, dblU_smul, dblX_smul, negY_smul, smul_fin3_ext]
  ring1

lemma negDblY_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negDblY P = -(P x ^ 2) ^ 3 := by
  linear_combination (norm :=
      (rw [negDblY, dblU_of_Z_eq_zero hPz, dblX_of_Z_eq_zero hP hPz, negY_of_Z_eq_zero hPz]; ring1))
    (8 * P y ^ 2 - 4 * P x ^ 3) * (equation_of_Z_eq_zero hPz).mp hP

-- DISSOLVED: negDblY_of_Y_eq

-- DISSOLVED: toAffine_negAddY_of_eq

-- DISSOLVED: negDblY_of_Z_ne_zero

variable (W') in

noncomputable def dblY (P : Fin 3 → R) : R :=
  W'.negY ![W'.dblX P, W'.negDblY P, W'.dblZ P]

lemma dblY_smul (P : Fin 3 → R) (u : R) : W'.dblY (u • P) = (u ^ 4) ^ 3 * W'.dblY P := by
  simp only [dblY, negY_eq, negDblY_smul, dblX_smul, dblZ_smul]
  ring1

lemma dblY_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblY P = (P x ^ 2) ^ 3 := by
  rw [dblY, negY_eq, negDblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz]
  ring1

-- DISSOLVED: dblY_of_Y_eq

-- DISSOLVED: dblY_of_Z_ne_zero

variable (W') in

noncomputable def dblXYZ (P : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblX P, W'.dblY P, W'.dblZ P]

lemma dblXYZ_smul (P : Fin 3 → R) (u : R) : W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P := by
  rw [dblXYZ, dblX_smul, dblY_smul, dblZ_smul, smul_fin3, dblXYZ_X, dblXYZ_Y, dblXYZ_Z]

lemma dblXYZ_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblXYZ P = P x ^ 2 • ![1, 1, 0] := by
  simp [dblXYZ, dblX_of_Z_eq_zero hP hPz, dblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz,
    smul_fin3]

-- DISSOLVED: dblXYZ_of_Y_eq'

-- DISSOLVED: dblXYZ_of_Y_eq

-- DISSOLVED: dblXYZ_of_Z_ne_zero

/-! ## Addition formulae in Jacobian coordinates -/

def addU (P Q : Fin 3 → F) : F :=
  -((P y * Q z ^ 3 - Q y * P z ^ 3) / (P z * Q z))

-- DISSOLVED: addU_smul

lemma addU_of_Z_eq_zero_left {P Q : Fin 3 → F} (hPz : P z = 0) : addU P Q = 0 := by
  rw [addU, hPz, zero_mul, div_zero, neg_zero]

lemma addU_of_Z_eq_zero_right {P Q : Fin 3 → F} (hQz : Q z = 0) : addU P Q = 0 := by
  rw [addU, hQz, mul_zero, div_zero, neg_zero]

-- DISSOLVED: addU_ne_zero_of_Y_ne

-- DISSOLVED: isUnit_addU_of_Y_ne

def addZ (P Q : Fin 3 → R) : R :=
  P x * Q z ^ 2 - Q x * P z ^ 2

lemma addZ_smul (P Q : Fin 3 → R) (u v : R) : addZ (u • P) (v • Q) = (u * v) ^ 2 * addZ P Q := by
  simp only [addZ, smul_fin3_ext]
  ring1

lemma addZ_self (P : Fin 3 → R) : addZ P P = 0 :=
  sub_self <| P x * P z ^ 2

lemma addZ_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) : addZ P Q = P x * Q z * Q z := by
  rw [addZ, hPz]
  ring1

lemma addZ_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQz : Q z = 0) :
    addZ P Q = -(Q x * P z) * P z := by
  rw [addZ, hQz]
  ring1

lemma addZ_of_X_eq {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 = Q x * P z ^ 2) : addZ P Q = 0 := by
  rw [addZ, hx, sub_self]

-- DISSOLVED: addZ_ne_zero_of_X_ne

lemma isUnit_addZ_of_X_ne {P Q : Fin 3 → F} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    IsUnit <| addZ P Q :=
  (addZ_ne_zero_of_X_ne hx).isUnit

-- DISSOLVED: toAffine_slope_of_ne

variable (W') in

def addX (P Q : Fin 3 → R) : R :=
  P x * Q x ^ 2 * P z ^ 2 - 2 * P y * Q y * P z * Q z + P x ^ 2 * Q x * Q z ^ 2
    - W'.a₁ * P x * Q y * P z ^ 2 * Q z - W'.a₁ * P y * Q x * P z * Q z ^ 2
    + 2 * W'.a₂ * P x * Q x * P z ^ 2 * Q z ^ 2 - W'.a₃ * Q y * P z ^ 4 * Q z
    - W'.a₃ * P y * P z * Q z ^ 4 + W'.a₄ * Q x * P z ^ 4 * Q z ^ 2
    + W'.a₄ * P x * P z ^ 2 * Q z ^ 4 + 2 * W'.a₆ * P z ^ 4 * Q z ^ 4

lemma addX_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * (P z * Q z) ^ 2 =
      (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2
        + W'.a₁ * (P y * Q z ^ 3 - Q y * P z ^ 3) * P z * Q z * addZ P Q
        - W'.a₂ * P z ^ 2 * Q z ^ 2 * addZ P Q ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2
        - Q x * P z ^ 2 * addZ P Q ^ 2 := by
  linear_combination (norm := (rw [addX, addZ]; ring1)) -Q z ^ 6 * (equation_iff P).mp hP
    - P z ^ 6 * (equation_iff Q).mp hQ

-- DISSOLVED: addX_eq

lemma addX_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addX (u • P) (v • Q) = ((u * v) ^ 2) ^ 2 * W'.addX P Q := by
  simp only [addX, smul_fin3_ext]
  ring1

lemma addX_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.addX P P = 0 := by
  linear_combination (norm := (rw [addX]; ring1)) -2 * P z ^ 2 * (equation_iff _).mp hP

lemma addX_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) :
    W'.addX P Q = (P x * Q z) ^ 2 * Q x := by
  rw [addX, hPz]
  ring1

lemma addX_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQz : Q z = 0) :
    W'.addX P Q = (-(Q x * P z)) ^ 2 * P x := by
  rw [addX, hQz]
  ring1

lemma addX_of_X_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W'.addX P Q * (P z * Q z) ^ 2 = (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2 := by
  rw [addX_eq' hP hQ, addZ_of_X_eq hx]
  ring1

-- DISSOLVED: addX_of_X_eq

-- DISSOLVED: toAffine_addX_of_ne

-- DISSOLVED: addX_of_Z_ne_zero

variable (W') in

def negAddY (P Q : Fin 3 → R) : R :=
  -P y * Q x ^ 3 * P z ^ 3 + 2 * P y * Q y ^ 2 * P z ^ 3 - 3 * P x ^ 2 * Q x * Q y * P z ^ 2 * Q z
    + 3 * P x * P y * Q x ^ 2 * P z * Q z ^ 2 + P x ^ 3 * Q y * Q z ^ 3
    - 2 * P y ^ 2 * Q y * Q z ^ 3 + W'.a₁ * P x * Q y ^ 2 * P z ^ 4
    + W'.a₁ * P y * Q x * Q y * P z ^ 3 * Q z - W'.a₁ * P x * P y * Q y * P z * Q z ^ 3
    - W'.a₁ * P y ^ 2 * Q x * Q z ^ 4 - 2 * W'.a₂ * P x * Q x * Q y * P z ^ 4 * Q z
    + 2 * W'.a₂ * P x * P y * Q x * P z * Q z ^ 4 + W'.a₃ * Q y ^ 2 * P z ^ 6
    - W'.a₃ * P y ^ 2 * Q z ^ 6 - W'.a₄ * Q x * Q y * P z ^ 6 * Q z
    - W'.a₄ * P x * Q y * P z ^ 4 * Q z ^ 3 + W'.a₄ * P y * Q x * P z ^ 3 * Q z ^ 4
    + W'.a₄ * P x * P y * P z * Q z ^ 6 - 2 * W'.a₆ * Q y * P z ^ 6 * Q z ^ 3
    + 2 * W'.a₆ * P y * P z ^ 3 * Q z ^ 6

lemma negAddY_eq' (P Q : Fin 3 → R) : W'.negAddY P Q * (P z * Q z) ^ 3 =
    (P y * Q z ^ 3 - Q y * P z ^ 3) * (W'.addX P Q * (P z * Q z) ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2)
      + P y * Q z ^ 3 * addZ P Q ^ 3 := by
  rw [negAddY, addX, addZ]
  ring1

-- DISSOLVED: negAddY_eq

lemma negAddY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.negAddY (u • P) (v • Q) = ((u * v) ^ 2) ^ 3 * W'.negAddY P Q := by
  simp only [negAddY, smul_fin3_ext]
  ring1

lemma negAddY_self (P : Fin 3 → R) : W'.negAddY P P = 0 := by
  rw [negAddY]
  ring1

lemma negAddY_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negAddY P Q = (P x * Q z) ^ 3 * W'.negY Q := by
  linear_combination (norm := (rw [negAddY, negY, hPz]; ring1))
    (W'.negY Q - Q y) * Q z ^ 3 * (equation_of_Z_eq_zero hPz).mp hP

lemma negAddY_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : W'.Equation Q) (hQz : Q z = 0) :
    W'.negAddY P Q = (-(Q x * P z)) ^ 3 * W'.negY P := by
  linear_combination (norm := (rw [negAddY, negY, hQz]; ring1))
    (P y - W'.negY P) * P z ^ 3 * (equation_of_Z_eq_zero hQz).mp hQ

lemma negAddY_of_X_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W'.negAddY P Q * (P z * Q z) ^ 3 = (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 3 := by
  rw [negAddY_eq', addX_eq' hP hQ, addZ_of_X_eq hx]
  ring1

-- DISSOLVED: negAddY_of_X_eq

-- DISSOLVED: toAffine_negAddY_of_ne

-- DISSOLVED: negAddY_of_Z_ne_zero

variable (W') in

def addY (P Q : Fin 3 → R) : R :=
  W'.negY ![W'.addX P Q, W'.negAddY P Q, addZ P Q]

lemma addY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addY (u • P) (v • Q) = ((u * v) ^ 2) ^ 3 * W'.addY P Q := by
  simp only [addY, negY_eq, negAddY_smul, addX_smul, addZ_smul]
  ring1

lemma addY_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P P = 0 := by
  rw [addY, negY_eq, addX_self hP, negAddY_self, addZ_self]
  ring1

lemma addY_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.addY P Q = (P x * Q z) ^ 3 * Q y := by
  rw [addY, negY_eq, negAddY_of_Z_eq_zero_left hP hPz, negY, addX_of_Z_eq_zero_left hPz,
    addZ_of_Z_eq_zero_left hPz]
  ring1

lemma addY_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : W'.Equation Q) (hQz : Q z = 0) :
    W'.addY P Q = (-(Q x * P z)) ^ 3 * P y := by
  rw [addY, negY_eq, negAddY_of_Z_eq_zero_right hQ hQz, negY, addX_of_Z_eq_zero_right hQz,
    addZ_of_Z_eq_zero_right hQz]
  ring1

lemma addY_of_X_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W'.addY P Q * (P z * Q z) ^ 3 = (-(P y * Q z ^ 3 - Q y * P z ^ 3)) ^ 3 := by
  linear_combination (norm := (rw [addY, negY_eq, addZ_of_X_eq hx]; ring1))
    -negAddY_of_X_eq' hP hQ hx

-- DISSOLVED: addY_of_X_eq

-- DISSOLVED: addY_of_Z_ne_zero

variable (W') in

noncomputable def addXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.addX P Q, W'.addY P Q, addZ P Q]

lemma addXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.addXYZ P Q := by
  rw [addXYZ, addX_smul, addY_smul, addZ_smul, smul_fin3, addXYZ_X, addXYZ_Y, addXYZ_Z]

lemma addXYZ_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.addXYZ P P = ![0, 0, 0] := by
  rw [addXYZ, addX_self hP, addY_self hP, addZ_self]

lemma addXYZ_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.addXYZ P Q = (P x * Q z) • Q := by
  rw [addXYZ, addX_of_Z_eq_zero_left hPz, addY_of_Z_eq_zero_left hP hPz, addZ_of_Z_eq_zero_left hPz,
    smul_fin3]

lemma addXYZ_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : W'.Equation Q) (hQz : Q z = 0) :
    W'.addXYZ P Q = -(Q x * P z) • P := by
  rw [addXYZ, addX_of_Z_eq_zero_right hQz, addY_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQz, smul_fin3]

-- DISSOLVED: addXYZ_of_X_eq

-- DISSOLVED: addXYZ_of_Z_ne_zero

/-! ## Maps and base changes -/

variable (f : R →+* S) (P Q : Fin 3 → R)
