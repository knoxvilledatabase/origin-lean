/-
Extracted from AlgebraicGeometry/EllipticCurve/Projective/Basic.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Weierstrass equations and the nonsingular condition in projective coordinates

A point on the unweighted projective plane over a commutative ring `R` is an equivalence class
`[x : y : z]` of triples `(x, y, z) ≠ (0, 0, 0)` of elements in `R` such that
`(x, y, z) ∼ (x', y', z')` if there is some unit `u` in `Rˣ` with `(x, y, z) = (ux', uy', uz')`.

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. A
*projective point* is a point on the unweighted projective plane over `R` satisfying the
*homogeneous Weierstrass equation* `W(X, Y, Z) = 0` in *projective coordinates*, where
`W(X, Y, Z) := Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`. It is *nonsingular* if its
partial derivatives `W_X(x, y, z)`, `W_Y(x, y, z)`, and `W_Z(x, y, z)` do not vanish simultaneously.

This file gives an explicit implementation of equivalence classes of triples up to scaling by units,
and defines polynomials associated to Weierstrass equations and the nonsingular condition in
projective coordinates. The group law on the actual type of nonsingular projective points will be
defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`, based on the formulae
for group operations in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean`.

## Main definitions

* `WeierstrassCurve.Projective.PointClass`: the equivalence class of a point representative.
* `WeierstrassCurve.Projective.Nonsingular`: the nonsingular condition on a point representative.
* `WeierstrassCurve.Projective.NonsingularLift`: the nonsingular condition on a point class.

## Main statements

* `WeierstrassCurve.Projective.polynomial_relation`: Euler's homogeneous function theorem.

## Implementation notes

All definitions and lemmas for Weierstrass curves in projective coordinates live in the namespace
`WeierstrassCurve.Projective` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toProjective`.
This can be converted into `WeierstrassCurve.Affine` using `WeierstrassCurve.Projective.toAffine`.

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not definitionally equivalent to the expanded vector
`![P x, P y, P z]`, so the lemmas `fin3_def` and `fin3_def_ext` can be used to convert between the
two forms. The equivalence of two point representatives `P` and `Q` is implemented as an equivalence
of orbits of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that
`P = u • Q`. However, `u • Q` is not definitionally equal to `![u * Q x, u * Q y, u * Q z]`, so the
lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms. Files in
`Mathlib/AlgebraicGeometry/EllipticCurve/Projective` make extensive use of `erw` to get around this.
While `erw` is often an indication of a problem, in this case it is self-contained and should not
cause any issues. It would alternatively be possible to add some automation to assist here.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, projective, Weierstrass equation, nonsingular
-/

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "eval_simp" : tactic =>

  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

local macro "map_simp" : tactic =>

  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,

    map_div₀, WeierstrassCurve.map, Function.comp_apply])

local macro "matrix_simp" : tactic =>

  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,

    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

local macro "pderiv_simp" : tactic =>

  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, pderiv_mul, pderiv_pow,

    pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero, pderiv_X_of_ne one_ne_zero.symm,

    pderiv_X_of_ne (by decide : z ≠ x), pderiv_X_of_ne (by decide : x ≠ z),

    pderiv_X_of_ne (by decide : z ≠ y), pderiv_X_of_ne (by decide : y ≠ z)])

universe r s u v

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v}

name_poly_vars X, Y, Z over R

namespace WeierstrassCurve

/-! ## Projective coordinates -/

variable (R) in

abbrev Projective : Type r :=
  WeierstrassCurve R

abbrev toProjective (W : WeierstrassCurve R) : Projective R :=
  W

namespace Projective

abbrev toAffine (W' : Projective R) : Affine R :=
  W'

lemma fin3_def (P : Fin 3 → R) : ![P x, P y, P z] = P := by
  ext n; fin_cases n <;> rfl

lemma fin3_def_ext (a b c : R) : ![a, b, c] x = a ∧ ![a, b, c] y = b ∧ ![a, b, c] z = c :=
  ⟨rfl, rfl, rfl⟩

lemma comp_fin3 (f : R → S) (a b c : R) : f ∘ ![a, b, c] = ![f a, f b, f c] :=
  (FinVec.map_eq ..).symm

variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] {W' : Projective R}
  {W : Projective F}

lemma smul_fin3 (P : Fin 3 → R) (u : R) : u • P = ![u * P x, u * P y, u * P z] := by
  simp [← List.ofFn_inj, List.ofFn_succ]

lemma smul_fin3_ext (P : Fin 3 → R) (u : R) :
    (u • P) x = u * P x ∧ (u • P) y = u * P y ∧ (u • P) z = u * P z :=
  ⟨rfl, rfl, rfl⟩

lemma comp_smul (f : R →+* S) (P : Fin 3 → R) (u : R) : f ∘ (u • P) = f u • f ∘ P := by
  ext
  simp
