/-
Extracted from AlgebraicGeometry/EllipticCurve/Projective/Point.lean
Genuine: 28 of 46 | Dissolved: 12 | Infrastructure: 6
-/
import Origin.Core

/-!
# Nonsingular points and the group law in projective coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular projective points of `W` can be
endowed with a group law, which is uniquely determined by the formulae in
`Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean` and follows from an equivalence
with the nonsingular points `W⟮F⟯` in affine coordinates.

This file defines the group law on nonsingular projective points.

## Main definitions

* `WeierstrassCurve.Projective.neg`: the negation of a point representative.
* `WeierstrassCurve.Projective.negMap`: the negation of a point class.
* `WeierstrassCurve.Projective.add`: the addition of two point representatives.
* `WeierstrassCurve.Projective.addMap`: the addition of two point classes.
* `WeierstrassCurve.Projective.Point`: a nonsingular projective point.
* `WeierstrassCurve.Projective.Point.neg`: the negation of a nonsingular projective point.
* `WeierstrassCurve.Projective.Point.add`: the addition of two nonsingular projective points.
* `WeierstrassCurve.Projective.Point.toAffineAddEquiv`: the equivalence between the type of
  nonsingular projective points with the type of nonsingular points `W⟮F⟯` in affine coordinates.

## Main statements

* `WeierstrassCurve.Projective.nonsingular_neg`: negation preserves the nonsingular condition.
* `WeierstrassCurve.Projective.nonsingular_add`: addition preserves the nonsingular condition.
* `WeierstrassCurve.Projective.Point.instAddCommGroup`: the type of nonsingular projective points
  forms an abelian group under addition.

## Implementation notes

Note that `W(X, Y, Z)` and its partial derivatives are independent of the point representative, and
the nonsingularity condition already implies `(x, y, z) ≠ (0, 0, 0)`, so a nonsingular projective
point on `W` can be given by `[x : y : z]` and the nonsingular condition on any representative.

A nonsingular projective point representative can be converted to a nonsingular point in affine
coordinates using `WeierstrassCurve.Projective.Point.toAffine`, which lifts to a map on nonsingular
projective points using `WeierstrassCurve.Projective.Point.toAffineLift`. Conversely, a nonsingular
point in affine coordinates can be converted to a nonsingular projective point using
`WeierstrassCurve.Projective.Point.fromAffine` or `WeierstrassCurve.Affine.Point.toProjective`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, projective, point, group law
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

/-! ## Negation on projective point representatives -/

variable (W') in

def neg (P : Fin 3 → R) : Fin 3 → R :=
  ![P x, W'.negY P, P z]

protected lemma neg_smul (P : Fin 3 → R) (u : R) : W'.neg (u • P) = u • W'.neg P := by
  simpa only [neg, negY_smul] using (smul_fin3 (W'.neg P) u).symm

lemma neg_smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈ W'.neg P :=
  ⟨hu.unit, (W'.neg_smul ..).symm⟩

lemma neg_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.neg P ≈ W'.neg Q := by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u.isUnit

lemma neg_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.neg P = -P y • ![0, 1, 0] := by
  simp [neg, X_eq_zero_of_Z_eq_zero hP hPz, negY_of_Z_eq_zero hP hPz, hPz]

-- DISSOLVED: neg_of_Z_ne_zero

-- DISSOLVED: nonsingular_neg_of_Z_ne_zero

lemma nonsingular_neg {P : Fin 3 → F} (hP : W.Nonsingular P) : W.Nonsingular <| W.neg P := by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP.left hPz, nonsingular_smul _ (isUnit_Y_of_Z_eq_zero hP hPz).neg,
      nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul _ <| Ne.isUnit hPz,
      nonsingular_neg_of_Z_ne_zero hP hPz]

lemma addZ_neg (P : Fin 3 → R) : W'.addZ P (W'.neg P) = 0 := by
  rw [addZ, neg_X, neg_Y, neg_Z, negY]
  ring1

lemma addX_neg (P : Fin 3 → R) : W'.addX P (W'.neg P) = 0 := by
  rw [addX, neg_X, neg_Y, neg_Z, negY]
  ring1

lemma negAddY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.negAddY P (W'.neg P) = W'.dblZ P := by
  linear_combination (norm := (rw [negAddY, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -3 * (P y - W'.negY P) * (equation_iff _).mp hP

lemma addY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P (W'.neg P) = -W'.dblZ P := by
  simp only [addY, addX_neg, negAddY_neg hP, addZ_neg, negY, fin3_def_ext, mul_zero, sub_zero]

lemma addXYZ_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.addXYZ P (W'.neg P) = -W'.dblZ P • ![0, 1, 0] := by
  erw [addXYZ, addX_neg, addY_neg hP, addZ_neg, smul_fin3, mul_zero, mul_one]

variable (W') in

def negMap (P : PointClass R) : PointClass R :=
  P.map W'.neg fun _ _ => neg_equiv

lemma negMap_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.negMap ⟦P⟧ = ⟦![0, 1, 0]⟧ := by
  rw [negMap_eq, neg_of_Z_eq_zero hP.left hPz, smul_eq _ (isUnit_Y_of_Z_eq_zero hP hPz).neg]

-- DISSOLVED: negMap_of_Z_ne_zero

lemma nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) :
    W.NonsingularLift <| W.negMap P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

/-! ## Addition on projective point representatives -/

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
    (hPz : P z = 0) (hQz : Q z = 0) : W.add P Q = P y ^ 4 • ![0, 1, 0] := by
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
        nonsingular_smul _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4, nonsingular_zero]
    · simpa only [add_of_Z_eq_zero_left hP.left hPz hQz,
        nonsingular_smul _ <| ((isUnit_Y_of_Z_eq_zero hP hPz).pow 2).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · simpa only [add_of_Z_eq_zero_right hQ.left hPz hQz,
        nonsingular_smul _ (((isUnit_Y_of_Z_eq_zero hQ hQz).pow 2).mul <| Ne.isUnit hPz).neg]
    · by_cases hxy : P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z
      · by_cases hy : P y * Q z = Q y * P z
        · simp only [add_of_Y_eq hP.left hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            nonsingular_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]
      · classical
        have := nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z = Q x * P z
        · simpa only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            nonsingular_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hQz hx <|
              not_and.mp hxy hx]
        · simpa only [add_of_X_ne hP.left hQ.left hPz hQz hx,
            nonsingular_smul _ <| isUnit_addZ_of_X_ne hP.left hQ.left hx]

variable (W') in

noncomputable def addMap (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

lemma addMap_of_Z_eq_zero_left {P : Fin 3 → F} {Q : PointClass F} (hP : W.Nonsingular P)
    (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q := by
  revert hQ
  refine Q.inductionOn (motive := fun Q => _ → W.addMap _ Q = Q) fun Q hQ => ?_
  by_cases hQz : Q z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hQ hQz
  · rw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
      smul_eq _ <| ((isUnit_Y_of_Z_eq_zero hP hPz).pow 2).mul <| Ne.isUnit hQz]

lemma addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 → F} (hP : W.NonsingularLift P)
    (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P := by
  revert hP
  refine P.inductionOn (motive := fun P => _ → W.addMap P _ = P) fun P hP => ?_
  by_cases hPz : P z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
  · rw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ (((isUnit_Y_of_Z_eq_zero hQ hQz).pow 2).mul <| Ne.isUnit hPz).neg]

-- DISSOLVED: addMap_of_Y_eq

-- DISSOLVED: addMap_of_Z_ne_zero

lemma nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P)
    (hQ : W.NonsingularLift Q) : W.NonsingularLift <| W.addMap P Q := by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

/-! ## Nonsingular projective points -/

variable (W') in
