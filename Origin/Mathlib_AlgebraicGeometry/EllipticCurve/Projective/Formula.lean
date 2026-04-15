/-
Extracted from AlgebraicGeometry/EllipticCurve/Projective/Formula.lean
Genuine: 60 of 116 | Dissolved: 49 | Infrastructure: 7
-/
import Origin.Core

/-!
# Negation and addition formulae for nonsingular points in projective coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular projective points on `W` can be
given negation and addition operations defined by an analogue of the secant-and-tangent process in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`, but the polynomials involved are
homogeneous, so any instances of division become multiplication in the `Z`-coordinate. Most
computational proofs are immediate from their analogous proofs for affine coordinates.

This file defines polynomials associated to negation, doubling, and addition of projective point
representatives. The group operations and the group law on actual nonsingular projective points will
be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`.

## Main definitions

* `WeierstrassCurve.Projective.negY`: the `Y`-coordinate of `-P`.
* `WeierstrassCurve.Projective.dblZ`: the `Z`-coordinate of `2 • P`.
* `WeierstrassCurve.Projective.dblX`: the `X`-coordinate of `2 • P`.
* `WeierstrassCurve.Projective.negDblY`: the `Y`-coordinate of `-(2 • P)`.
* `WeierstrassCurve.Projective.dblY`: the `Y`-coordinate of `2 • P`.
* `WeierstrassCurve.Projective.addZ`: the `Z`-coordinate of `P + Q`.
* `WeierstrassCurve.Projective.addX`: the `X`-coordinate of `P + Q`.
* `WeierstrassCurve.Projective.negAddY`: the `Y`-coordinate of `-(P + Q)`.
* `WeierstrassCurve.Projective.addY`: the `Y`-coordinate of `P + Q`.

## Implementation notes

The definitions of `WeierstrassCurve.Projective.dblX`, `WeierstrassCurve.Projective.negDblY`,
`WeierstrassCurve.Projective.addZ`, `WeierstrassCurve.Projective.addX`, and
`WeierstrassCurve.Projective.negAddY` are given explicitly by large polynomials that are homogeneous
of degree `4`. Clearing the denominators of their corresponding affine rational functions in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean` would give polynomials that are
homogeneous of degrees `5`, `6`, `6`, `8`, and `8` respectively, so their actual definitions are off
by powers of certain polynomial factors that are homogeneous of degree `1` or `2`. These factors
divide their corresponding affine polynomials only modulo the homogeneous Weierstrass equation, so
their large quotient polynomials are calculated explicitly in a computer algebra system. All of this
is done to ensure that the definitions of both `WeierstrassCurve.Projective.dblXYZ` and
`WeierstrassCurve.Projective.addXYZ` are homogeneous of degree `4`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, projective, negation, doubling, addition, group law
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
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Projective R} {W : Projective F}

namespace Projective

/-! ## Negation formulae in projective coordinates -/

variable (W') in

def negY (P : Fin 3 → R) : R :=
  -P y - W'.a₁ * P x - W'.a₃ * P z

lemma negY_smul (P : Fin 3 → R) (u : R) : W'.negY (u • P) = u * W'.negY P := by
  simp only [negY, smul_fin3_ext]
  ring1

lemma negY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negY P = -P y := by
  rw [negY, hPz, X_eq_zero_of_Z_eq_zero hP hPz, mul_zero, sub_zero, mul_zero, sub_zero]

-- DISSOLVED: negY_of_Z_ne_zero

lemma Y_sub_Y_mul_Y_sub_negY {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z = Q x * P z) :
    P z * Q z * (P y * Q z - Q y * P z) * (P y * Q z - W'.negY Q * P z) = 0 := by
  linear_combination (norm := (rw [negY]; ring1)) Q z ^ 3 * (equation_iff P).mp hP
    - P z ^ 3 * (equation_iff Q).mp hQ + (P x ^ 2 * Q z ^ 2 + P x * Q x * P z * Q z
      + Q x ^ 2 * P z ^ 2 - W'.a₁ * P y * P z * Q z ^ 2 + W'.a₂ * P x * Q z ^ 2 * P z
      + W'.a₂ * Q x * P z ^ 2 * Q z + W'.a₄ * P z ^ 2 * Q z ^ 2) * hx

-- DISSOLVED: Y_eq_of_Y_ne

-- DISSOLVED: Y_eq_of_Y_ne'

-- DISSOLVED: Y_eq_iff'

lemma Y_sub_Y_add_Y_sub_negY {P Q : Fin 3 → R} (hx : P x * Q z = Q x * P z) :
    (P y * Q z - Q y * P z) + (P y * Q z - W'.negY Q * P z) = (P y - W'.negY P) * Q z := by
  linear_combination (norm := (rw [negY, negY]; ring1)) -W'.a₁ * hx

-- DISSOLVED: Y_ne_negY_of_Y_ne

-- DISSOLVED: Y_ne_negY_of_Y_ne'

-- DISSOLVED: Y_eq_negY_of_Y_eq

-- DISSOLVED: nonsingular_iff_of_Y_eq_negY

/-! ## Doubling formulae in projective coordinates -/

variable (W) in

noncomputable def dblU (P : Fin 3 → F) : F :=
  eval P W.polynomialX ^ 3 / P z ^ 2

lemma dblU_eq (P : Fin 3 → F) : W.dblU P =
    (W.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W.a₂ * P x * P z + W.a₄ * P z ^ 2)) ^ 3 / P z ^ 2 := by
  rw [dblU, eval_polynomialX]

lemma dblU_smul (P : Fin 3 → F) (u : F) :
    W.dblU (u • P) = u ^ 4 * W.dblU P := by
  simp [field, dblU_eq]

lemma dblU_of_Z_eq_zero {P : Fin 3 → F} (hPz : P z = 0) : W.dblU P = 0 := by
  rw [dblU_eq, hPz, zero_pow two_ne_zero, div_zero]

-- DISSOLVED: dblU_ne_zero_of_Y_eq

-- DISSOLVED: isUnit_dblU_of_Y_eq

variable (W') in

def dblZ (P : Fin 3 → R) : R :=
  P z * (P y - W'.negY P) ^ 3

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
  2 * P x * P y ^ 3 + 3 * W'.a₁ * P x ^ 2 * P y ^ 2 + 6 * W'.a₂ * P x ^ 3 * P y
    - 8 * W'.a₂ * P y ^ 3 * P z + 9 * W'.a₃ * P x ^ 4 - 6 * W'.a₃ * P x * P y ^ 2 * P z
    - 6 * W'.a₄ * P x ^ 2 * P y * P z - 18 * W'.a₆ * P x * P y * P z ^ 2
    + 3 * W'.a₁ ^ 2 * P x ^ 3 * P y - 2 * W'.a₁ ^ 2 * P y ^ 3 * P z + 3 * W'.a₁ * W'.a₂ * P x ^ 4
    - 12 * W'.a₁ * W'.a₂ * P x * P y ^ 2 * P z - 9 * W'.a₁ * W'.a₃ * P x ^ 2 * P y * P z
    - 3 * W'.a₁ * W'.a₄ * P x ^ 3 * P z - 9 * W'.a₁ * W'.a₆ * P x ^ 2 * P z ^ 2
    + 8 * W'.a₂ ^ 2 * P x ^ 2 * P y * P z + 12 * W'.a₂ * W'.a₃ * P x ^ 3 * P z
    - 12 * W'.a₂ * W'.a₃ * P y ^ 2 * P z ^ 2 + 8 * W'.a₂ * W'.a₄ * P x * P y * P z ^ 2
    - 12 * W'.a₃ ^ 2 * P x * P y * P z ^ 2 + 6 * W'.a₃ * W'.a₄ * P x ^ 2 * P z ^ 2
    + 2 * W'.a₄ ^ 2 * P y * P z ^ 3 + W'.a₁ ^ 3 * P x ^ 4 - 3 * W'.a₁ ^ 3 * P x * P y ^ 2 * P z
    - 2 * W'.a₁ ^ 2 * W'.a₂ * P x ^ 2 * P y * P z - 3 * W'.a₁ ^ 2 * W'.a₃ * P y ^ 2 * P z ^ 2
    + 2 * W'.a₁ ^ 2 * W'.a₄ * P x * P y * P z ^ 2 + 4 * W'.a₁ * W'.a₂ ^ 2 * P x ^ 3 * P z
    - 8 * W'.a₁ * W'.a₂ * W'.a₃ * P x * P y * P z ^ 2
    + 4 * W'.a₁ * W'.a₂ * W'.a₄ * P x ^ 2 * P z ^ 2 - 3 * W'.a₁ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2
    + 2 * W'.a₁ * W'.a₃ * W'.a₄ * P y * P z ^ 3 + W'.a₁ * W'.a₄ ^ 2 * P x * P z ^ 3
    + 4 * W'.a₂ ^ 2 * W'.a₃ * P x ^ 2 * P z ^ 2 - 6 * W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3
    + 4 * W'.a₂ * W'.a₃ * W'.a₄ * P x * P z ^ 3 - 2 * W'.a₃ ^ 3 * P x * P z ^ 3
    + W'.a₃ * W'.a₄ ^ 2 * P z ^ 4 - W'.a₁ ^ 4 * P x ^ 2 * P y * P z
    + W'.a₁ ^ 3 * W'.a₂ * P x ^ 3 * P z - 2 * W'.a₁ ^ 3 * W'.a₃ * P x * P y * P z ^ 2
    + W'.a₁ ^ 3 * W'.a₄ * P x ^ 2 * P z ^ 2 + W'.a₁ ^ 2 * W'.a₂ * W'.a₃ * P x ^ 2 * P z ^ 2
    - W'.a₁ ^ 2 * W'.a₃ ^ 2 * P y * P z ^ 3 + 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P x * P z ^ 3
    - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P x * P z ^ 3 - W'.a₂ * W'.a₃ ^ 3 * P z ^ 4
    + W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4

lemma dblX_eq' {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblX P * P z =
    (eval P W'.polynomialX ^ 2 - W'.a₁ * eval P W'.polynomialX * P z * (P y - W'.negY P)
      - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * P z * (P y - W'.negY P) ^ 2)
      * (P y - W'.negY P) := by
  linear_combination (norm := (rw [dblX, eval_polynomialX, negY]; ring1))
    9 * (W'.a₁ * P x ^ 2 + 2 * P x * P y) * (equation_iff _).mp hP

-- DISSOLVED: dblX_eq

lemma dblX_smul (P : Fin 3 → R) (u : R) : W'.dblX (u • P) = u ^ 4 * W'.dblX P := by
  simp only [dblX, smul_fin3_ext]
  ring1

lemma dblX_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblX P = 0 := by
  rw [dblX, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

-- DISSOLVED: dblX_of_Y_eq

set_option linter.flexible false in

-- DISSOLVED: toAffine_addX_of_eq

-- DISSOLVED: dblX_of_Z_ne_zero

variable (W') in

noncomputable def negDblY (P : Fin 3 → R) : R :=
  -P y ^ 4 - 3 * W'.a₁ * P x * P y ^ 3 - 9 * W'.a₃ * P x ^ 3 * P y + 3 * W'.a₃ * P y ^ 3 * P z
    - 3 * W'.a₄ * P x * P y ^ 2 * P z - 27 * W'.a₆ * P x ^ 3 * P z + 9 * W'.a₆ * P y ^ 2 * P z ^ 2
    - 3 * W'.a₁ ^ 2 * P x ^ 2 * P y ^ 2 + 4 * W'.a₁ * W'.a₂ * P y ^ 3 * P z
    - 3 * W'.a₁ * W'.a₂ * P x ^ 3 * P y - 9 * W'.a₁ * W'.a₃ * P x ^ 4
    + 6 * W'.a₁ * W'.a₃ * P x * P y ^ 2 * P z + 18 * W'.a₁ * W'.a₆ * P x * P y * P z ^ 2
    + 9 * W'.a₂ ^ 2 * P x ^ 4 - 8 * W'.a₂ ^ 2 * P x * P y ^ 2 * P z
    - 9 * W'.a₂ * W'.a₃ * P x ^ 2 * P y * P z + 9 * W'.a₂ * W'.a₄ * P x ^ 3 * P z
    - 4 * W'.a₂ * W'.a₄ * P y ^ 2 * P z ^ 2 - 27 * W'.a₂ * W'.a₆ * P x ^ 2 * P z ^ 2
    - 9 * W'.a₃ ^ 2 * P x ^ 3 * P z + 6 * W'.a₃ ^ 2 * P y ^ 2 * P z ^ 2
    - 12 * W'.a₃ * W'.a₄ * P x * P y * P z ^ 2 + 9 * W'.a₄ ^ 2 * P x ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 3 * P x ^ 3 * P y + W'.a₁ ^ 3 * P y ^ 3 * P z + 3 * W'.a₁ ^ 2 * W'.a₂ * P x ^ 4
    + 2 * W'.a₁ ^ 2 * W'.a₂ * P x * P y ^ 2 * P z + 3 * W'.a₁ ^ 2 * W'.a₃ * P x ^ 2 * P y * P z
    + 3 * W'.a₁ ^ 2 * W'.a₄ * P x ^ 3 * P z - W'.a₁ ^ 2 * W'.a₄ * P y ^ 2 * P z ^ 2
    - 12 * W'.a₁ * W'.a₂ ^ 2 * P x ^ 2 * P y * P z - 6 * W'.a₁ * W'.a₂ * W'.a₃ * P x ^ 3 * P z
    + 4 * W'.a₁ * W'.a₂ * W'.a₃ * P y ^ 2 * P z ^ 2
    - 8 * W'.a₁ * W'.a₂ * W'.a₄ * P x * P y * P z ^ 2 + 6 * W'.a₁ * W'.a₃ ^ 2 * P x * P y * P z ^ 2
    - W'.a₁ * W'.a₄ ^ 2 * P y * P z ^ 3 + 8 * W'.a₂ ^ 3 * P x ^ 3 * P z
    - 8 * W'.a₂ ^ 2 * W'.a₃ * P x * P y * P z ^ 2 + 12 * W'.a₂ ^ 2 * W'.a₄ * P x ^ 2 * P z ^ 2
    - 9 * W'.a₂ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 - 4 * W'.a₂ * W'.a₃ * W'.a₄ * P y * P z ^ 3
    + 6 * W'.a₂ * W'.a₄ ^ 2 * P x * P z ^ 3 + W'.a₃ ^ 3 * P y * P z ^ 3
    - 3 * W'.a₃ ^ 2 * W'.a₄ * P x * P z ^ 3 + W'.a₄ ^ 3 * P z ^ 4 + W'.a₁ ^ 4 * P x * P y ^ 2 * P z
    - 3 * W'.a₁ ^ 3 * W'.a₂ * P x ^ 2 * P y * P z + W'.a₁ ^ 3 * W'.a₃ * P y ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 3 * W'.a₄ * P x * P y * P z ^ 2 + 2 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * P x ^ 3 * P z
    - 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ * P x * P y * P z ^ 2
    + 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ * P x ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P y * P z ^ 3 + W'.a₁ ^ 2 * W'.a₄ ^ 2 * P x * P z ^ 3
    + W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3 + 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P x * P z ^ 3
    + W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P z ^ 4 - 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * P z ^ 3
    - W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4

lemma negDblY_eq' {P : Fin 3 → R} (hP : W'.Equation P) : W'.negDblY P * P z ^ 2 =
    -eval P W'.polynomialX * (eval P W'.polynomialX ^ 2
      - W'.a₁ * eval P W'.polynomialX * P z * (P y - W'.negY P)
      - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * P z * (P y - W'.negY P) ^ 2
      - P x * P z * (P y - W'.negY P) ^ 2) + P y * P z ^ 2 * (P y - W'.negY P) ^ 3 := by
  linear_combination (norm := (rw [negDblY, eval_polynomialX, negY]; ring1))
    -9 * (P y ^ 2 * P z + 2 * W'.a₁ * P x * P y * P z - 3 * P x ^ 3 - 3 * W'.a₂ * P x ^ 2 * P z)
      * (equation_iff _).mp hP

-- DISSOLVED: negDblY_eq

lemma negDblY_smul (P : Fin 3 → R) (u : R) : W'.negDblY (u • P) = u ^ 4 * W'.negDblY P := by
  simp only [negDblY, smul_fin3_ext]
  ring1

lemma negDblY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negDblY P = -P y ^ 4 := by
  rw [negDblY, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

-- DISSOLVED: negDblY_of_Y_eq'

-- DISSOLVED: negDblY_of_Y_eq

-- DISSOLVED: toAffine_negAddY_of_eq

-- DISSOLVED: negDblY_of_Z_ne_zero

variable (W') in

noncomputable def dblY (P : Fin 3 → R) : R :=
  W'.negY ![W'.dblX P, W'.negDblY P, W'.dblZ P]

lemma dblY_smul (P : Fin 3 → R) (u : R) : W'.dblY (u • P) = u ^ 4 * W'.dblY P := by
  simp only [dblY, negY_eq, negDblY_smul, dblX_smul, dblZ_smul]
  ring1

lemma dblY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblY P = P y ^ 4 := by
  rw [dblY, negY_eq, negDblY_of_Z_eq_zero hP hPz, dblX_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz]
  ring1

-- DISSOLVED: dblY_of_Y_eq'

-- DISSOLVED: dblY_of_Y_eq

-- DISSOLVED: dblY_of_Z_ne_zero

variable (W') in

noncomputable def dblXYZ (P : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblX P, W'.dblY P, W'.dblZ P]

lemma dblXYZ_smul (P : Fin 3 → R) (u : R) : W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P := by
  rw [dblXYZ, dblX_smul, dblY_smul, dblZ_smul, smul_fin3, dblXYZ_X, dblXYZ_Y, dblXYZ_Z]

lemma dblXYZ_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblXYZ P = P y ^ 4 • ![0, 1, 0] := by
  erw [dblXYZ, dblX_of_Z_eq_zero hP hPz, dblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz, smul_fin3,
    mul_zero, mul_one]

-- DISSOLVED: dblXYZ_of_Y_eq

-- DISSOLVED: dblXYZ_of_Z_ne_zero

/-! ## Addition formulae in projective coordinates -/

def addU (P Q : Fin 3 → F) : F :=
  -(P y * Q z - Q y * P z) ^ 3 / (P z * Q z)

lemma addU_smul (P Q : Fin 3 → F) (u v : F) : addU (u • P) (v • Q) = (u * v) ^ 2 * addU P Q := by
  simp [field, addU]

lemma addU_of_Z_eq_zero_left {P Q : Fin 3 → F} (hPz : P z = 0) : addU P Q = 0 := by
  rw [addU, hPz, zero_mul, div_zero]

lemma addU_of_Z_eq_zero_right {P Q : Fin 3 → F} (hQz : Q z = 0) : addU P Q = 0 := by
  rw [addU, hQz, mul_zero <| P z, div_zero]

-- DISSOLVED: addU_ne_zero_of_Y_ne

-- DISSOLVED: isUnit_addU_of_Y_ne

variable (W') in

def addZ (P Q : Fin 3 → R) : R :=
  -3 * P x ^ 2 * Q x * Q z + 3 * P x * Q x ^ 2 * P z + P y ^ 2 * Q z ^ 2 - Q y ^ 2 * P z ^ 2
    + W'.a₁ * P x * P y * Q z ^ 2 - W'.a₁ * Q x * Q y * P z ^ 2 - W'.a₂ * P x ^ 2 * Q z ^ 2
    + W'.a₂ * Q x ^ 2 * P z ^ 2 + W'.a₃ * P y * P z * Q z ^ 2 - W'.a₃ * Q y * P z ^ 2 * Q z
    - W'.a₄ * P x * P z * Q z ^ 2 + W'.a₄ * Q x * P z ^ 2 * Q z

lemma addZ_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addZ P Q * (P z * Q z) = (P x * Q z - Q x * P z) ^ 3 := by
  linear_combination (norm := (rw [addZ]; ring1))
    Q z ^ 3 * (equation_iff _).mp hP - P z ^ 3 * (equation_iff _).mp hQ

-- DISSOLVED: addZ_eq

lemma addZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addZ (u • P) (v • Q) = (u * v) ^ 2 * W'.addZ P Q := by
  simp only [addZ, smul_fin3_ext]
  ring1

lemma addZ_self (P : Fin 3 → R) : W'.addZ P P = 0 := by
  rw [addZ]
  ring1

lemma addZ_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addZ P Q = P y ^ 2 * Q z * Q z := by
  rw [addZ, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

lemma addZ_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addZ P Q = -(Q y ^ 2 * P z) * P z := by
  rw [addZ, hQz, X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

-- DISSOLVED: addZ_of_X_eq

-- DISSOLVED: addZ_ne_zero_of_X_ne

lemma isUnit_addZ_of_X_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hx : P x * Q z ≠ Q x * P z) : IsUnit <| W.addZ P Q :=
  (addZ_ne_zero_of_X_ne hP hQ hx).isUnit

-- DISSOLVED: toAffine_slope_of_ne

variable (W') in

def addX (P Q : Fin 3 → R) : R :=
  -P x * Q y ^ 2 * P z + Q x * P y ^ 2 * Q z - 2 * P x * P y * Q y * Q z + 2 * Q x * P y * Q y * P z
    - W'.a₁ * P x ^ 2 * Q y * Q z + W'.a₁ * Q x ^ 2 * P y * P z + W'.a₂ * P x ^ 2 * Q x * Q z
    - W'.a₂ * P x * Q x ^ 2 * P z - W'.a₃ * P x * P y * Q z ^ 2 + W'.a₃ * Q x * Q y * P z ^ 2
    - 2 * W'.a₃ * P x * Q y * P z * Q z + 2 * W'.a₃ * Q x * P y * P z * Q z
    + W'.a₄ * P x ^ 2 * Q z ^ 2 - W'.a₄ * Q x ^ 2 * P z ^ 2 + 3 * W'.a₆ * P x * P z * Q z ^ 2
    - 3 * W'.a₆ * Q x * P z ^ 2 * Q z

lemma addX_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * (P z * Q z) ^ 2 =
      ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W'.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2) * (P x * Q z - Q x * P z) := by
  linear_combination (norm := (rw [addX]; ring1))
    (2 * Q x * P z * Q z ^ 3 - P x * Q z ^ 4) * (equation_iff _).mp hP
      + (Q x * P z ^ 4 - 2 * P x * P z ^ 3 * Q z) * (equation_iff _).mp hQ

-- DISSOLVED: addX_eq

lemma addX_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addX (u • P) (v • Q) = (u * v) ^ 2 * W'.addX P Q := by
  simp only [addX, smul_fin3_ext]
  ring1

lemma addX_self (P : Fin 3 → R) : W'.addX P P = 0 := by
  rw [addX]
  ring1

lemma addX_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addX P Q = P y ^ 2 * Q z * Q x := by
  rw [addX, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

lemma addX_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addX P Q = -(Q y ^ 2 * P z) * P x := by
  rw [addX, hQz, X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

-- DISSOLVED: addX_of_X_eq

-- DISSOLVED: toAffine_addX_of_ne

-- DISSOLVED: addX_of_Z_ne_zero

variable (W') in

def negAddY (P Q : Fin 3 → R) : R :=
  -3 * P x ^ 2 * Q x * Q y + 3 * P x * Q x ^ 2 * P y - P y ^ 2 * Q y * Q z + P y * Q y ^ 2 * P z
    + W'.a₁ * P x * Q y ^ 2 * P z - W'.a₁ * Q x * P y ^ 2 * Q z - W'.a₂ * P x ^ 2 * Q y * Q z
    + W'.a₂ * Q x ^ 2 * P y * P z + 2 * W'.a₂ * P x * Q x * P y * Q z
    - 2 * W'.a₂ * P x * Q x * Q y * P z - W'.a₃ * P y ^ 2 * Q z ^ 2 + W'.a₃ * Q y ^ 2 * P z ^ 2
    + W'.a₄ * P x * P y * Q z ^ 2 - 2 * W'.a₄ * P x * Q y * P z * Q z
    + 2 * W'.a₄ * Q x * P y * P z * Q z - W'.a₄ * Q x * Q y * P z ^ 2
    + 3 * W'.a₆ * P y * P z * Q z ^ 2 - 3 * W'.a₆ * Q y * P z ^ 2 * Q z

lemma negAddY_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.negAddY P Q * (P z * Q z) ^ 2 =
      (P y * Q z - Q y * P z) * ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W'.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2)
        + P y * Q z * (P x * Q z - Q x * P z) ^ 3 := by
  linear_combination (norm := (rw [negAddY]; ring1))
    (2 * Q y * P z * Q z ^ 3 - P y * Q z ^ 4) * (equation_iff _).mp hP
      + (Q y * P z ^ 4 - 2 * P y * P z ^ 3 * Q z) * (equation_iff _).mp hQ

-- DISSOLVED: negAddY_eq

lemma negAddY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.negAddY (u • P) (v • Q) = (u * v) ^ 2 * W'.negAddY P Q := by
  simp only [negAddY, smul_fin3_ext]
  ring1

lemma negAddY_self (P : Fin 3 → R) : W'.negAddY P P = 0 := by
  rw [negAddY]
  ring1

lemma negAddY_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.negAddY P Q = P y ^ 2 * Q z * W'.negY Q := by
  rw [negAddY, hPz, X_eq_zero_of_Z_eq_zero hP hPz, negY]
  ring1

lemma negAddY_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.negAddY P Q = -(Q y ^ 2 * P z) * W'.negY P := by
  rw [negAddY, hQz, X_eq_zero_of_Z_eq_zero hQ hQz, negY]
  ring1

lemma negAddY_of_X_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z = Q x * P z) :
    W'.negAddY P Q * (P z * Q z) ^ 2 = (P y * Q z - Q y * P z) ^ 3 * (P z * Q z) := by
  rw [negAddY_eq' hP hQ, hx]
  ring1

-- DISSOLVED: negAddY_of_X_eq

-- DISSOLVED: toAffine_negAddY_of_ne

-- DISSOLVED: negAddY_of_Z_ne_zero

variable (W') in

def addY (P Q : Fin 3 → R) : R :=
  W'.negY ![W'.addX P Q, W'.negAddY P Q, W'.addZ P Q]

lemma addY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addY (u • P) (v • Q) = (u * v) ^ 2 * W'.addY P Q := by
  simp only [addY, negY_eq, negAddY_smul, addX_smul, addZ_smul]
  ring1

lemma addY_self (P : Fin 3 → R) : W'.addY P P = 0 := by
  simp only [addY, negY_eq, negAddY_self, addX_self, addZ_self, neg_zero, mul_zero, sub_zero]

lemma addY_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addY P Q = P y ^ 2 * Q z * Q y := by
  rw [addY, negY_eq, negAddY_of_Z_eq_zero_left hP hPz, negY, addX_of_Z_eq_zero_left hP hPz,
    addZ_of_Z_eq_zero_left hP hPz]
  ring1

lemma addY_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addY P Q = -(Q y ^ 2 * P z) * P y := by
  rw [addY, negY_eq, negAddY_of_Z_eq_zero_right hQ hQz, negY, addX_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQ hQz]
  ring1

-- DISSOLVED: addY_of_X_eq'

-- DISSOLVED: addY_of_X_eq

-- DISSOLVED: addY_of_Z_ne_zero

variable (W') in

noncomputable def addXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.addX P Q, W'.addY P Q, W'.addZ P Q]

lemma addXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.addXYZ P Q := by
  rw [addXYZ, addX_smul, addY_smul, addZ_smul, smul_fin3, addXYZ_X, addXYZ_Y, addXYZ_Z]

lemma addXYZ_self (P : Fin 3 → R) : W'.addXYZ P P = ![0, 0, 0] := by
  rw [addXYZ, addX_self, addY_self, addZ_self]

lemma addXYZ_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addXYZ P Q = (P y ^ 2 * Q z) • Q := by
  rw [addXYZ, addX_of_Z_eq_zero_left hP hPz, addY_of_Z_eq_zero_left hP hPz,
    addZ_of_Z_eq_zero_left hP hPz, smul_fin3]

lemma addXYZ_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addXYZ P Q = -(Q y ^ 2 * P z) • P := by
  rw [addXYZ, addX_of_Z_eq_zero_right hQ hQz, addY_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQ hQz, smul_fin3]

-- DISSOLVED: addXYZ_of_X_eq

-- DISSOLVED: addXYZ_of_Z_ne_zero

/-! ## Maps and base changes -/

variable (f : R →+* S) (P Q : Fin 3 → R)
