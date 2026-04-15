/-
Extracted from AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean
Genuine: 29 of 47 | Dissolved: 12 | Infrastructure: 6
-/
import Origin.Core

/-!
# Nonsingular points and the group law in Jacobian coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular Jacobian points of `W` can be
endowed with a group law, which is uniquely determined by the formulae in
`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean` and follows from an equivalence with
the nonsingular points `W⟮F⟯` in affine coordinates.

This file defines the group law on nonsingular Jacobian points.

## Main definitions

* `WeierstrassCurve.Jacobian.neg`: the negation of a point representative.
* `WeierstrassCurve.Jacobian.negMap`: the negation of a point class.
* `WeierstrassCurve.Jacobian.add`: the addition of two point representatives.
* `WeierstrassCurve.Jacobian.addMap`: the addition of two point classes.
* `WeierstrassCurve.Jacobian.Point`: a nonsingular Jacobian point.
* `WeierstrassCurve.Jacobian.Point.neg`: the negation of a nonsingular Jacobian point.
* `WeierstrassCurve.Jacobian.Point.add`: the addition of two nonsingular Jacobian points.
* `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`: the equivalence between the type of
  nonsingular Jacobian points with the type of nonsingular points `W⟮F⟯` in affine coordinates.

## Main statements

* `WeierstrassCurve.Jacobian.nonsingular_neg`: negation preserves the nonsingular condition.
* `WeierstrassCurve.Jacobian.nonsingular_add`: addition preserves the nonsingular condition.
* `WeierstrassCurve.Jacobian.Point.instAddCommGroup`: the type of nonsingular Jacobian points forms
  an abelian group under addition.

## Implementation notes

Note that `W(X, Y, Z)` and its partial derivatives are independent of the point representative, and
the nonsingularity condition already implies `(x, y, z) ≠ (0, 0, 0)`, so a nonsingular Jacobian
point on `W` can be given by `[x : y : z]` and the nonsingular condition on any representative.

A nonsingular Jacobian point representative can be converted to a nonsingular point in affine
coordinates using `WeierstrassCurve.Jacobian.Point.toAffine`, which lifts to a map on nonsingular
Jacobian points using `WeierstrassCurve.Jacobian.Point.toAffineLift`. Conversely, a nonsingular
point in affine coordinates can be converted to a nonsingular Jacobian point using
`WeierstrassCurve.Jacobian.Point.fromAffine` or `WeierstrassCurve.Affine.Point.toJacobian`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, point, group law
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

/-! ## Negation on Jacobian point representatives -/

variable (W') in

def neg (P : Fin 3 → R) : Fin 3 → R :=
  ![P x, W'.negY P, P z]

protected lemma neg_smul (P : Fin 3 → R) (u : R) : W'.neg (u • P) = u • W'.neg P := by
  rw [neg, negY_smul]
  rfl

lemma neg_smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈ W'.neg P :=
  ⟨hu.unit, (W'.neg_smul ..).symm⟩

lemma neg_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.neg P ≈ W'.neg Q := by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u.isUnit

lemma neg_of_Z_eq_zero' {P : Fin 3 → R} (hPz : P z = 0) : W'.neg P = ![P x, -P y, 0] := by
  rw [neg, negY_of_Z_eq_zero hPz, hPz]

lemma neg_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.neg P = -(P y / P x) • ![1, 1, 0] := by
  have hX {n : ℕ} : IsUnit <| P x ^ n := (isUnit_X_of_Z_eq_zero hP hPz).pow n
  erw [neg_of_Z_eq_zero' hPz, smul_fin3, neg_sq, div_pow, (equation_of_Z_eq_zero hPz).mp hP.left,
    pow_succ, hX.mul_div_cancel_left, mul_one, Odd.neg_pow <| by decide, div_pow, pow_succ,
    (equation_of_Z_eq_zero hPz).mp hP.left, hX.mul_div_cancel_left, mul_one, mul_zero]

-- DISSOLVED: neg_of_Z_ne_zero

-- DISSOLVED: nonsingular_neg_of_Z_ne_zero

lemma nonsingular_neg {P : Fin 3 → F} (hP : W.Nonsingular P) : W.Nonsingular <| W.neg P := by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP hPz, nonsingular_smul _
        ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg, nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul _ <| Ne.isUnit hPz,
      nonsingular_neg_of_Z_ne_zero hP hPz]

lemma addZ_neg (P : Fin 3 → R) : addZ P (W'.neg P) = 0 :=
  addZ_of_X_eq rfl

lemma addX_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addX P (W'.neg P) = W'.dblZ P ^ 2 := by
  linear_combination (norm := (rw [addX, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 2 * (equation_iff _).mp hP

lemma negAddY_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.negAddY P (W'.neg P) = W'.dblZ P ^ 3 := by
  linear_combination (norm := (rw [negAddY, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 3 * (P y - W'.negY P) * (equation_iff _).mp hP

lemma addY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P (W'.neg P) = -W'.dblZ P ^ 3 := by
  rw [addY, addX_neg hP, negAddY_neg hP, addZ_neg, negY_of_Z_eq_zero rfl]
  rfl

lemma addXYZ_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.addXYZ P (W'.neg P) = -W'.dblZ P • ![1, 1, 0] := by
  erw [addXYZ, addX_neg hP, addY_neg hP, addZ_neg, smul_fin3, neg_sq, mul_one,
    Odd.neg_pow <| by decide, mul_one, mul_zero]

variable (W') in

def negMap (P : PointClass R) : PointClass R :=
  P.map W'.neg fun _ _ => neg_equiv

lemma negMap_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.negMap ⟦P⟧ = ⟦![1, 1, 0]⟧ := by
  rw [negMap_eq, neg_of_Z_eq_zero hP hPz,
    smul_eq _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg]

-- DISSOLVED: negMap_of_Z_ne_zero

lemma nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) :
    W.NonsingularLift <| W.negMap P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

/-! ## Addition on Jacobian point representatives -/

open scoped Classical in

variable (W') in

noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q

lemma add_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.add P Q = W'.dblXYZ P :=
  if_pos h

lemma add_smul_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) = u ^ 4 • W'.add P Q := by
  rw [add_of_equiv <| (smul_equiv_smul P Q hu hv).mpr h, dblXYZ_smul, add_of_equiv h]

lemma add_self (P : Fin 3 → R) : W'.add P P = W'.dblXYZ P :=
  add_of_equiv <| Setoid.refl _

lemma add_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q :=
  if_neg h

lemma add_smul_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) {u v : R} (hu : IsUnit u)
    (hv : IsUnit v) : W'.add (u • P) (v • Q) = (u * v) ^ 2 • W'.add P Q := by
  rw [add_of_not_equiv <| h.comp (smul_equiv_smul P Q hu hv).mp, addXYZ_smul, add_of_not_equiv h]

lemma add_smul_equiv (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) ≈ W'.add P Q := by
  by_cases h : P ≈ Q
  · exact ⟨hu.unit ^ 4, by convert (add_smul_of_equiv h hu hv).symm⟩
  · exact ⟨(hu.unit * hv.unit) ^ 2, by convert (add_smul_of_not_equiv h hu hv).symm⟩

lemma add_equiv {P P' Q Q' : Fin 3 → R} (hP : P ≈ P') (hQ : Q ≈ Q') :
    W'.add P Q ≈ W'.add P' Q' := by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact add_smul_equiv P' Q' u.isUnit v.isUnit

lemma add_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : W.add P Q = P x ^ 2 • ![1, 1, 0] := by
  rw [add_of_equiv <| equiv_of_Z_eq_zero hP hQ hPz hQz, dblXYZ_of_Z_eq_zero hP.left hPz]

-- DISSOLVED: add_of_Z_eq_zero_left

-- DISSOLVED: add_of_Z_eq_zero_right

-- DISSOLVED: add_of_Y_eq

-- DISSOLVED: add_of_Y_ne

-- DISSOLVED: add_of_Y_ne'

-- DISSOLVED: add_of_X_ne

-- DISSOLVED: nonsingular_add_of_Z_ne_zero

lemma nonsingular_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Nonsingular <| W.add P Q := by
  by_cases hPz : P z = 0
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero hP hQ hPz hQz,
        nonsingular_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, nonsingular_zero]
    · simpa only [add_of_Z_eq_zero_left hP.left hPz hQz,
        nonsingular_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · simpa only [add_of_Z_eq_zero_right hQ.left hPz hQz,
        nonsingular_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · simp only [add_of_Y_eq hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            nonsingular_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]
      · classical
        have := nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · simpa only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            nonsingular_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx <| not_and.mp hxy hx]
        · simpa only [add_of_X_ne hP.left hQ.left hPz hQz hx,
            nonsingular_smul _ <| isUnit_addZ_of_X_ne hx]

variable (W') in

noncomputable def addMap (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

lemma addMap_of_Z_eq_zero_left {P : Fin 3 → F} {Q : PointClass F} (hP : W.Nonsingular P)
    (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q := by
  revert hQ
  refine Q.inductionOn (motive := fun Q => _ → W.addMap _ Q = Q) fun Q hQ => ?_
  by_cases hQz : Q z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hQ hQz
  · rw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]

lemma addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 → F} (hP : W.NonsingularLift P)
    (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P := by
  revert hP
  refine P.inductionOn (motive := fun P => _ → W.addMap P _ = P) fun P hP => ?_
  by_cases hPz : P z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
  · rw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]

-- DISSOLVED: addMap_of_Y_eq

-- DISSOLVED: addMap_of_Z_ne_zero

lemma nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P)
    (hQ : W.NonsingularLift Q) : W.NonsingularLift <| W.addMap P Q := by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

/-! ## Nonsingular Jacobian points -/

variable (W') in
