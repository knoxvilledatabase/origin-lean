/-
Extracted from AlgebraicGeometry/EllipticCurve/Jacobian.lean
Genuine: 174 of 268 | Dissolved: 77 | Infrastructure: 17
-/
import Origin.Core
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.LinearCombination'

/-!
# Jacobian coordinates for Weierstrass curves

This file defines the type of points on a Weierstrass curve as a tuple, consisting of an equivalence
class of triples up to scaling by weights, satisfying a Weierstrass equation with a nonsingular
condition. This file also defines the negation and addition operations of the group law for this
type, and proves that they respect the Weierstrass equation and the nonsingular condition. The fact
that they form an abelian group is proven in `Mathlib.AlgebraicGeometry.EllipticCurve.Group`.

## Mathematical background

Let `W` be a Weierstrass curve over a field `F`. A point on the weighted projective plane with
weights $(2, 3, 1)$ is an equivalence class of triples $[x:y:z]$ with coordinates in `F` such that
$(x, y, z) \sim (x', y', z')$ precisely if there is some unit `u` of `F` such that
$(x, y, z) = (u^2x', u^3y', uz')$, with an extra condition that $(x, y, z) \ne (0, 0, 0)$.
A rational point is a point on the $(2, 3, 1)$-projective plane satisfying a $(2, 3, 1)$-homogeneous
Weierstrass equation $Y^2 + a_1XYZ + a_3YZ^3 = X^3 + a_2X^2Z^2 + a_4XZ^4 + a_6Z^6$, and being
nonsingular means the partial derivatives $W_X(X, Y, Z)$, $W_Y(X, Y, Z)$, and $W_Z(X, Y, Z)$ do not
vanish simultaneously. Note that the vanishing of the Weierstrass equation and its partial
derivatives are independent of the representative for $[x:y:z]$, and the nonsingularity condition
already implies that $(x, y, z) \ne (0, 0, 0)$, so a nonsingular rational point on `W` can simply be
given by a tuple consisting of $[x:y:z]$ and the nonsingular condition on any representative.
In cryptography, as well as in this file, this is often called the Jacobian coordinates of `W`.

As in `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`, the set of nonsingular rational points forms
an abelian group under the same secant-and-tangent process, but the polynomials involved are
$(2, 3, 1)$-homogeneous, and any instances of division become multiplication in the $Z$-coordinate.
Note that most computational proofs follow from their analogous proofs for affine coordinates.

## Main definitions

 * `WeierstrassCurve.Jacobian.PointClass`: the equivalence class of a point representative.
 * `WeierstrassCurve.Jacobian.toAffine`: the Weierstrass curve in affine coordinates.
 * `WeierstrassCurve.Jacobian.Nonsingular`: the nonsingular condition on a point representative.
 * `WeierstrassCurve.Jacobian.NonsingularLift`: the nonsingular condition on a point class.
 * `WeierstrassCurve.Jacobian.neg`: the negation operation on a point representative.
 * `WeierstrassCurve.Jacobian.negMap`: the negation operation on a point class.
 * `WeierstrassCurve.Jacobian.add`: the addition operation on a point representative.
 * `WeierstrassCurve.Jacobian.addMap`: the addition operation on a point class.
 * `WeierstrassCurve.Jacobian.Point`: a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.neg`: the negation operation on a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.add`: the addition operation on a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`: the equivalence between the nonsingular
    rational points on a Weierstrass curve in Jacobian coordinates with those in affine coordinates.

## Main statements

 * `WeierstrassCurve.Jacobian.NonsingularNeg`: negation preserves the nonsingular condition.
 * `WeierstrassCurve.Jacobian.NonsingularAdd`: addition preserves the nonsingular condition.

## Implementation notes

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not syntactically equivalent to the expanded vector
`![P x, P y, P z]`, so the lemmas `fin3_def` and `fin3_def_ext` can be used to convert between the
two forms. The equivalence of two point representatives `P` and `Q` is implemented as an equivalence
of orbits of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that
`P = u • Q`. However, `u • Q` is not syntactically equal to `![u² * Q x, u³ * Q y, u * Q z]`, so the
lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, Jacobian coordinates
-/

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

universe u v

/-! ## Weierstrass curves -/

abbrev WeierstrassCurve.Jacobian (R : Type u) : Type u :=
  WeierstrassCurve R

abbrev WeierstrassCurve.toJacobian {R : Type u} (W : WeierstrassCurve R) : Jacobian R :=
  W

namespace WeierstrassCurve.Jacobian

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

local macro "pderiv_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero, pderiv_X_of_ne one_ne_zero.symm,
    pderiv_X_of_ne (by decide : z ≠ x), pderiv_X_of_ne (by decide : x ≠ z),
    pderiv_X_of_ne (by decide : z ≠ y), pderiv_X_of_ne (by decide : y ≠ z)])

variable {R : Type u} {W' : Jacobian R} {F : Type v} [Field F] {W : Jacobian F}

section Jacobian

/-! ### Jacobian coordinates -/

lemma fin3_def (P : Fin 3 → R) : ![P x, P y, P z] = P := by
  ext n; fin_cases n <;> rfl

lemma fin3_def_ext (X Y Z : R) : ![X, Y, Z] x = X ∧ ![X, Y, Z] y = Y ∧ ![X, Y, Z] z = Z :=
  ⟨rfl, rfl, rfl⟩

lemma comp_fin3 {S} (f : R → S) (X Y Z : R) : f ∘ ![X, Y, Z] = ![f X, f Y, f Z] :=
  (FinVec.map_eq _ _).symm

variable [CommRing R]

scoped instance instSMulPoint : SMul R <| Fin 3 → R :=
  ⟨fun u P => ![u ^ 2 * P x, u ^ 3 * P y, u * P z]⟩

lemma smul_fin3 (P : Fin 3 → R) (u : R) : u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z] :=
  rfl

lemma smul_fin3_ext (P : Fin 3 → R) (u : R) :
    (u • P) x = u ^ 2 * P x ∧ (u • P) y = u ^ 3 * P y ∧ (u • P) z = u * P z :=
  ⟨rfl, rfl, rfl⟩

scoped instance instMulActionPoint : MulAction R <| Fin 3 → R where
  one_smul _ := by simp_rw [smul_fin3, one_pow, one_mul, fin3_def]
  mul_smul _ _ _ := by simp_rw [smul_fin3, mul_pow, mul_assoc, fin3_def_ext]

scoped instance instSetoidPoint : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

variable (R) in

abbrev PointClass : Type u :=
  MulAction.orbitRel.Quotient Rˣ <| Fin 3 → R

lemma smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : u • P ≈ P :=
  ⟨hu.unit, rfl⟩

@[simp]
lemma smul_eq (P : Fin 3 → R) {u : R} (hu : IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧ :=
  Quotient.eq.mpr <| smul_equiv P hu

variable (W') in

abbrev toAffine : Affine R :=
  W'

lemma equiv_iff_eq_of_Z_eq' {P Q : Fin 3 → R} (hz : P z = Q z) (mem : Q z ∈ nonZeroDivisors R) :
    P ≈ Q ↔ P = Q := by
  refine ⟨?_, by rintro rfl; exact Setoid.refl _⟩
  rintro ⟨u, rfl⟩
  rw [← one_mul (Q z)] at hz
  simp_rw [Units.smul_def, (mul_cancel_right_mem_nonZeroDivisors mem).mp hz, one_smul]

-- DISSOLVED: equiv_iff_eq_of_Z_eq

lemma Z_eq_zero_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0 := by
  rcases h with ⟨_, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext, Units.mul_right_eq_zero]

lemma X_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P x * Q z ^ 2 = Q x * P z ^ 2 := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

lemma Y_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P y * Q z ^ 3 = Q y * P z ^ 3 := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

-- DISSOLVED: not_equiv_of_Z_eq_zero_left

-- DISSOLVED: not_equiv_of_Z_eq_zero_right

lemma not_equiv_of_X_ne {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : ¬P ≈ Q :=
  hx.comp X_eq_of_equiv

lemma not_equiv_of_Y_ne {P Q : Fin 3 → R} (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : ¬P ≈ Q :=
  hy.comp Y_eq_of_equiv

-- DISSOLVED: equiv_of_X_eq_of_Y_eq

-- DISSOLVED: equiv_some_of_Z_ne_zero

-- DISSOLVED: X_eq_iff

-- DISSOLVED: Y_eq_iff

end Jacobian

variable [CommRing R]

section Equation

/-! ### Weierstrass equations -/

variable (W') in

noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C W'.a₁ * X 0 * X 1 * X 2 + C W'.a₃ * X 1 * X 2 ^ 3
    - (X 0 ^ 3 + C W'.a₂ * X 0 ^ 2 * X 2 ^ 2 + C W'.a₄ * X 0 * X 2 ^ 4 + C W'.a₆ * X 2 ^ 6)

lemma eval_polynomial (P : Fin 3 → R) : eval P W'.polynomial =
    P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6) := by
  rw [polynomial]
  eval_simp

-- DISSOLVED: eval_polynomial_of_Z_ne_zero

variable (W') in

def Equation (P : Fin 3 → R) : Prop :=
  eval P W'.polynomial = 0

lemma equation_iff (P : Fin 3 → R) : W'.Equation P ↔
    P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6) = 0 := by
  rw [Equation, eval_polynomial]

lemma equation_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P :=
  have (u : R) {P : Fin 3 → R} (hP : W'.Equation P) : W'.Equation <| u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) u ^ 6 * hP
  ⟨fun h => by convert this hu.unit.inv h; erw [smul_smul, hu.val_inv_mul, one_smul], this u⟩

lemma equation_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equation Q := by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit

lemma equation_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    W'.Equation P ↔ P y ^ 2 = P x ^ 3 := by
  simp only [equation_iff, hPz, add_zero, mul_zero, zero_pow <| OfNat.ofNat_ne_zero _, sub_eq_zero]

lemma equation_zero : W'.Equation ![1, 1, 0] := by
  simp only [equation_of_Z_eq_zero, fin3_def_ext, one_pow]

lemma equation_some (X Y : R) : W'.Equation ![X, Y, 1] ↔ W'.toAffine.Equation X Y := by
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext, one_pow, mul_one]

-- DISSOLVED: equation_of_Z_ne_zero

end Equation

section Nonsingular

/-! ### Nonsingular Weierstrass equations -/

variable (W') in

noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv x W'.polynomial

lemma polynomialX_eq : W'.polynomialX =
    C W'.a₁ * X 1 * X 2 - (C 3 * X 0 ^ 2 + C (2 * W'.a₂) * X 0 * X 2 ^ 2 + C W'.a₄ * X 2 ^ 4) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialX (P : Fin 3 → R) : eval P W'.polynomialX =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) := by
  rw [polynomialX_eq]
  eval_simp

-- DISSOLVED: eval_polynomialX_of_Z_ne_zero

variable (W') in

noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv y W'.polynomial

lemma polynomialY_eq : W'.polynomialY = C 2 * X 1 + C W'.a₁ * X 0 * X 2 + C W'.a₃ * X 2 ^ 3 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialY (P : Fin 3 → R) :
    eval P W'.polynomialY = 2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3 := by
  rw [polynomialY_eq]
  eval_simp

-- DISSOLVED: eval_polynomialY_of_Z_ne_zero

variable (W') in

noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv z W'.polynomial

lemma polynomialZ_eq : W'.polynomialZ = C W'.a₁ * X 0 * X 1 + C (3 * W'.a₃) * X 1 * X 2 ^ 2 -
    (C (2 * W'.a₂) * X 0 ^ 2 * X 2 + C (4 * W'.a₄) * X 0 * X 2 ^ 3 + C (6 * W'.a₆) * X 2 ^ 5) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialZ (P : Fin 3 → R) : eval P W'.polynomialZ =
    W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2 -
      (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x * P z ^ 3 + 6 * W'.a₆ * P z ^ 5) := by
  rw [polynomialZ_eq]
  eval_simp

variable (W') in

def Nonsingular (P : Fin 3 → R) : Prop :=
  W'.Equation P ∧
    (eval P W'.polynomialX ≠ 0 ∨ eval P W'.polynomialY ≠ 0 ∨ eval P W'.polynomialZ ≠ 0)

-- DISSOLVED: nonsingular_iff

lemma nonsingular_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) :
    W'.Nonsingular (u • P) ↔ W'.Nonsingular P :=
  have {u : R} (hu : IsUnit u) {P : Fin 3 → R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    contrapose! hP'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) u ^ 4 * hP'.left,
      by linear_combination (norm := ring1) u ^ 3 * hP'.right.left,
      by linear_combination (norm := ring1) u ^ 5 * hP'.right.right⟩
  ⟨this hu, fun h => this hu.unit⁻¹.isUnit <| by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩

lemma nonsingular_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Nonsingular P ↔ W'.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit

-- DISSOLVED: nonsingular_of_Z_eq_zero

lemma nonsingular_zero [Nontrivial R] : W'.Nonsingular ![1, 1, 0] := by
  simp only [nonsingular_of_Z_eq_zero, equation_zero, true_and, fin3_def_ext, ← not_and_or]
  exact fun h => one_ne_zero <| by linear_combination (norm := ring1) h.1 - h.2.1

lemma nonsingular_some (X Y : R) : W'.Nonsingular ![X, Y, 1] ↔ W'.toAffine.Nonsingular X Y := by
  simp_rw [nonsingular_iff, equation_some, fin3_def_ext, Affine.nonsingular_iff',
    Affine.equation_iff', and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    and_congr_right_iff, Iff.comm, iff_self_and]
  intro h hX hY
  linear_combination (norm := ring1) 6 * h - 2 * X * hX - 3 * Y * hY

-- DISSOLVED: nonsingular_of_Z_ne_zero

-- DISSOLVED: nonsingular_iff_of_Z_ne_zero

-- DISSOLVED: X_ne_zero_of_Z_eq_zero

-- DISSOLVED: isUnit_X_of_Z_eq_zero

-- DISSOLVED: Y_ne_zero_of_Z_eq_zero

-- DISSOLVED: isUnit_Y_of_Z_eq_zero

lemma equiv_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  have hPx : IsUnit <| P x := isUnit_X_of_Z_eq_zero hP hPz
  have hPy : IsUnit <| P y := isUnit_Y_of_Z_eq_zero hP hPz
  have hQx : IsUnit <| Q x := isUnit_X_of_Z_eq_zero hQ hQz
  have hQy : IsUnit <| Q y := isUnit_Y_of_Z_eq_zero hQ hQz
  simp only [nonsingular_of_Z_eq_zero, equation_of_Z_eq_zero, hPz, hQz] at hP hQ
  use (hPy.unit / hPx.unit) * (hQx.unit / hQy.unit)
  simp only [Units.smul_def, smul_fin3, Units.val_mul, Units.val_div_eq_div_val, IsUnit.unit_spec,
    mul_pow, div_pow, hQz, mul_zero]
  conv_rhs => rw [← fin3_def P, hPz]
  congr! 2
  · rw [hP.left, pow_succ, (hPx.pow 2).mul_div_cancel_left, hQ.left, pow_succ _ 2,
      (hQx.pow 2).div_mul_cancel_left, hQx.inv_mul_cancel_right]
  · rw [← hP.left, pow_succ, (hPy.pow 2).mul_div_cancel_left, ← hQ.left, pow_succ _ 2,
      (hQy.pow 2).div_mul_cancel_left, hQy.inv_mul_cancel_right]

lemma equiv_zero_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ ![1, 1, 0] :=
  equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl

variable (W') in

def NonsingularLift (P : PointClass R) : Prop :=
  P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

lemma nonsingularLift_iff (P : Fin 3 → R) : W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsingular P :=
  Iff.rfl

lemma nonsingularLift_zero [Nontrivial R] : W'.NonsingularLift ⟦![1, 1, 0]⟧ :=
  nonsingular_zero

lemma nonsingularLift_some (X Y : R) :
    W'.NonsingularLift ⟦![X, Y, 1]⟧ ↔ W'.toAffine.Nonsingular X Y :=
  nonsingular_some X Y

end Nonsingular

section Negation

/-! ### Negation formulae -/

variable (W') in

def negY (P : Fin 3 → R) : R :=
  -P y - W'.a₁ * P x * P z - W'.a₃ * P z ^ 3

lemma negY_smul (P : Fin 3 → R) {u : R} : W'.negY (u • P) = u ^ 3 * W'.negY P := by
  simp only [negY, smul_fin3_ext]
  ring1

lemma negY_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.negY P = -P y := by
  simp only [negY, hPz, sub_zero, mul_zero, zero_pow three_ne_zero]

-- DISSOLVED: negY_of_Z_ne_zero

lemma Y_sub_Y_mul_Y_sub_negY {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    (P y * Q z ^ 3 - Q y * P z ^ 3) * (P y * Q z ^ 3 - W'.negY Q * P z ^ 3) = 0 := by
  linear_combination' (norm := (rw [negY]; ring1)) Q z ^ 6 * (equation_iff P).mp hP
    - P z ^ 6 * (equation_iff Q).mp hQ + hx * hx * hx + W'.a₂ * P z ^ 2 * Q z ^ 2 * hx * hx
    + (W'.a₄ * P z ^ 4 * Q z ^ 4 - W'.a₁ * P y * P z * Q z ^ 4) * hx

lemma Y_eq_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    P y * Q z ^ 3 = W.negY Q * P z ^ 3 :=
  eq_of_sub_eq_zero <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left <|
    sub_ne_zero_of_ne hy

lemma Y_eq_of_Y_ne' {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    P y * Q z ^ 3 = Q y * P z ^ 3 :=
  eq_of_sub_eq_zero <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_right <|
    sub_ne_zero_of_ne hy

-- DISSOLVED: Y_eq_iff'

lemma Y_sub_Y_add_Y_sub_negY (P Q : Fin 3 → R) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    (P y * Q z ^ 3 - Q y * P z ^ 3) + (P y * Q z ^ 3 - W'.negY Q * P z ^ 3) =
      (P y - W'.negY P) * Q z ^ 3 := by
  linear_combination (norm := (rw [negY, negY]; ring1)) -W'.a₁ * P z * Q z * hx

lemma Y_ne_negY_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    P y ≠ W'.negY P := by
  have hy' : P y * Q z ^ 3 - W'.negY Q * P z ^ 3 = 0 :=
    (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left <| sub_ne_zero_of_ne hy
  contrapose! hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY P Q hx + Q z ^ 3 * hy - hy'

lemma Y_ne_negY_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ W'.negY Q * P z ^ 3) : P y ≠ W'.negY P := by
  have hy' : P y * Q z ^ 3 - Q y * P z ^ 3 = 0 :=
    (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_right <| sub_ne_zero_of_ne hy
  contrapose! hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY P Q hx + Q z ^ 3 * hy - hy'

-- DISSOLVED: Y_eq_negY_of_Y_eq

-- DISSOLVED: nonsingular_iff_of_Y_eq_negY

end Negation

section Doubling

/-! ### Doubling formulae -/

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
  simp_rw [dblX, dblU_smul, negY_smul, smul_fin3_ext]
  ring1

lemma dblX_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblX P = (P x ^ 2) ^ 2 := by
  linear_combination (norm := (rw [dblX, dblU_of_Z_eq_zero hPz, negY_of_Z_eq_zero hPz, hPz]; ring1))
    -8 * P x * (equation_of_Z_eq_zero hPz).mp hP

-- DISSOLVED: dblX_of_Y_eq

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
  linear_combination' (norm :=
      (rw [negDblY, dblU_of_Z_eq_zero hPz, dblX_of_Z_eq_zero hP hPz, negY_of_Z_eq_zero hPz]; ring1))
    (8 * (equation_of_Z_eq_zero hPz).mp hP - 12 * P x ^ 3) * (equation_of_Z_eq_zero hPz).mp hP

-- DISSOLVED: negDblY_of_Y_eq

-- DISSOLVED: toAffine_negAddY_of_eq

-- DISSOLVED: negDblY_of_Z_ne_zero

variable (W') in

noncomputable def dblY (P : Fin 3 → R) : R :=
  W'.negY ![W'.dblX P, W'.negDblY P, W'.dblZ P]

lemma dblY_smul (P : Fin 3 → R) (u : R) : W'.dblY (u • P) = (u ^ 4) ^ 3 * W'.dblY P := by
  simp only [dblY, negY, dblX_smul, negDblY_smul, dblZ_smul, fin3_def_ext]
  ring1

lemma dblY_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblY P = (P x ^ 2) ^ 3 := by
  erw [dblY, negDblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz, negY_of_Z_eq_zero rfl, neg_neg]

-- DISSOLVED: dblY_of_Y_eq

-- DISSOLVED: dblY_of_Z_ne_zero

variable (W') in

noncomputable def dblXYZ (P : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblX P, W'.dblY P, W'.dblZ P]

lemma dblXYZ_smul (P : Fin 3 → R) (u : R) : W'.dblXYZ (u • P) = (u ^ 4) • W'.dblXYZ P := by
  rw [dblXYZ, dblX_smul, dblY_smul, dblZ_smul]
  rfl

lemma dblXYZ_of_Z_eq_zero {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblXYZ P = P x ^ 2 • ![1, 1, 0] := by
  erw [dblXYZ, dblX_of_Z_eq_zero hP hPz, dblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz, smul_fin3,
    mul_one, mul_one, mul_zero]

-- DISSOLVED: dblXYZ_of_Y_eq'

-- DISSOLVED: dblXYZ_of_Y_eq

-- DISSOLVED: dblXYZ_of_Z_ne_zero

end Doubling

section Addition

/-! ### Addition formulae -/

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

lemma addZ_self {P : Fin 3 → R} : addZ P P = 0 := sub_self _

lemma addZ_smul (P Q : Fin 3 → R) (u v : R) : addZ (u • P) (v • Q) = (u * v) ^ 2 * addZ P Q := by
  simp only [addZ, smul_fin3_ext]
  ring1

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

lemma addX_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.addX P P = 0 := by
  linear_combination (norm := (rw [addX]; ring1)) -2 * P z ^ 2 * (equation_iff _).mp hP

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
  simp only [addX_eq' hP hQ, addZ_of_X_eq hx, add_zero, sub_zero, mul_zero, zero_pow two_ne_zero]

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

lemma negAddY_self {P : Fin 3 → R} : W'.negAddY P P = 0 := by rw [negAddY]; ring

lemma negAddY_eq' {P Q : Fin 3 → R} : W'.negAddY P Q * (P z * Q z) ^ 3 =
    (P y * Q z ^ 3 - Q y * P z ^ 3) * (W'.addX P Q * (P z * Q z) ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2)
      + P y * Q z ^ 3 * addZ P Q ^ 3 := by
  rw [negAddY, addX, addZ]
  ring1

-- DISSOLVED: negAddY_eq

lemma negAddY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.negAddY (u • P) (v • Q) = ((u * v) ^ 2) ^ 3 * W'.negAddY P Q := by
  simp only [negAddY, smul_fin3_ext]
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
  simp only [negAddY_eq', addX_eq' hP hQ, addZ_of_X_eq hx, add_zero, sub_zero, mul_zero,
    zero_pow <| OfNat.ofNat_ne_zero _, ← pow_succ']

-- DISSOLVED: negAddY_of_X_eq

-- DISSOLVED: toAffine_negAddY_of_ne

-- DISSOLVED: negAddY_of_Z_ne_zero

variable (W') in

def addY (P Q : Fin 3 → R) : R :=
  W'.negY ![W'.addX P Q, W'.negAddY P Q, addZ P Q]

lemma addY_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P P = 0 := by
  erw [addY, addX_self hP, negAddY_self, addZ_self, negY_of_Z_eq_zero rfl, neg_zero]

lemma addY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addY (u • P) (v • Q) = ((u * v) ^ 2) ^ 3 * W'.addY P Q := by
  simp only [addY, negY, addX_smul, negAddY_smul, addZ_smul, fin3_def_ext]
  ring1

lemma addY_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.addY P Q = (P x * Q z) ^ 3 * Q y := by
  simp only [addY, addX_of_Z_eq_zero_left hPz, negAddY_of_Z_eq_zero_left hP hPz,
    addZ_of_Z_eq_zero_left hPz, negY, fin3_def_ext]
  ring1

lemma addY_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : W'.Equation Q) (hQz : Q z = 0) :
    W'.addY P Q = (-(Q x * P z)) ^ 3 * P y := by
  simp only [addY, addX_of_Z_eq_zero_right hQz, negAddY_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQz, negY, fin3_def_ext]
  ring1

lemma addY_of_X_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W'.addY P Q * (P z * Q z) ^ 3 = (-(P y * Q z ^ 3 - Q y * P z ^ 3)) ^ 3 := by
  erw [addY, negY, addZ_of_X_eq hx, mul_zero, sub_zero, zero_pow three_ne_zero, mul_zero, sub_zero,
    neg_mul, negAddY_of_X_eq' hP hQ hx, Odd.neg_pow <| by decide]

-- DISSOLVED: addY_of_X_eq

-- DISSOLVED: addY_of_Z_ne_zero

variable (W') in

noncomputable def addXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.addX P Q, W'.addY P Q, addZ P Q]

lemma addXYZ_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.addXYZ P P = ![0, 0, 0] := by
  rw [addXYZ, addX_self hP, addY_self hP, addZ_self]

lemma addXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.addXYZ P Q := by
  rw [addXYZ, addX_smul, addY_smul, addZ_smul]
  rfl

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

end Addition

section Negation

/-! ### Negation on point representatives -/

variable (W') in

def neg (P : Fin 3 → R) : Fin 3 → R :=
  ![P x, W'.negY P, P z]

lemma neg_smul (P : Fin 3 → R) (u : R) : W'.neg (u • P) = u • W'.neg P := by
  rw [neg, negY_smul]
  rfl

lemma neg_smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈ W'.neg P :=
  ⟨hu.unit, (neg_smul ..).symm⟩

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

lemma addZ_neg {P : Fin 3 → R} : addZ P (W'.neg P) = 0 := addZ_of_X_eq rfl

lemma addX_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addX P (W'.neg P) = W'.dblZ P ^ 2 := by
  simp only [addX, neg, dblZ, negY, fin3_def_ext]
  linear_combination -2 * P z ^ 2 * (equation_iff _).mp hP

lemma negAddY_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.negAddY P (W'.neg P) = W'.dblZ P ^ 3 := by
  simp only [negAddY, neg, dblZ, negY, fin3_def_ext]
  linear_combination -2 * (2 * P y * P z ^ 3 + W'.a₁ * P x * P z ^ 4 + W'.a₃ * P z ^ 6)
    * (equation_iff _).mp hP

lemma addY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P (W'.neg P) = -W'.dblZ P ^ 3 := by
  rw [addY, addX_neg hP, negAddY_neg hP, negY_of_Z_eq_zero addZ_neg]; rfl

lemma addXYZ_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.addXYZ P (W'.neg P) = -W'.dblZ P • ![1, 1, 0] := by
  erw [addXYZ, addX_neg hP, addY_neg hP, addZ_neg, smul_fin3, neg_sq, mul_one,
    Odd.neg_pow <| by decide, mul_one, mul_zero]

variable (W') in

def negMap (P : PointClass R) : PointClass R :=
  P.map W'.neg fun _ _ => neg_equiv

lemma negMap_eq {P : Fin 3 → R} : W'.negMap ⟦P⟧ = ⟦W'.neg P⟧ :=
  rfl

lemma negMap_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.negMap ⟦P⟧ = ⟦![1, 1, 0]⟧ := by
  rw [negMap_eq, neg_of_Z_eq_zero hP hPz,
    smul_eq _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg]

-- DISSOLVED: negMap_of_Z_ne_zero

lemma nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) :
    W.NonsingularLift <| W.negMap P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

end Negation

section Addition

/-! ### Addition on point representatives -/

open Classical in

variable (W') in

noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q

lemma add_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.add P Q = W'.dblXYZ P :=
  if_pos h

lemma add_smul_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) = u ^ 4 • W'.add P Q := by
  have smul : P ≈ Q ↔ u • P ≈ v • Q := by
    erw [← Quotient.eq_iff_equiv, ← Quotient.eq_iff_equiv, smul_eq P hu, smul_eq Q hv]
    rfl
  rw [add_of_equiv <| smul.mp h, dblXYZ_smul, add_of_equiv h]

lemma add_self (P : Fin 3 → R) : W'.add P P = W'.dblXYZ P :=
  add_of_equiv <| Setoid.refl _

lemma add_of_eq {P Q : Fin 3 → R} (h : P = Q) : W'.add P Q = W'.dblXYZ P :=
  h ▸ add_self P

lemma add_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q :=
  if_neg h

lemma add_smul_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) {u v : R} (hu : IsUnit u)
    (hv : IsUnit v) : W'.add (u • P) (v • Q) = (u * v) ^ 2 • W'.add P Q := by
  have smul : P ≈ Q ↔ u • P ≈ v • Q := by
    erw [← Quotient.eq_iff_equiv, ← Quotient.eq_iff_equiv, smul_eq P hu, smul_eq Q hv]
    rfl
  rw [add_of_not_equiv <| h.comp smul.mpr, addXYZ_smul, add_of_not_equiv h]

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
  rw [add, if_pos <| equiv_of_Z_eq_zero hP hQ hPz hQz, dblXYZ_of_Z_eq_zero hP.left hPz]

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
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 → P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3
      · by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · simp only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| hxy hx,
            nonsingular_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx <| hxy hx,
            nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy]
        · simp only [add_of_X_ne hP.left hQ.left hPz hQz hx,
            nonsingular_smul _ <| isUnit_addZ_of_X_ne hx,
            nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy]
      · rw [_root_.not_imp, not_ne_iff] at hxy
        by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · simp only [add_of_Y_eq hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            nonsingular_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]

variable (W') in

noncomputable def addMap (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

lemma addMap_eq (P Q : Fin 3 → R) : W'.addMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧ :=
  rfl

lemma addMap_of_Z_eq_zero_left {P : Fin 3 → F} {Q : PointClass F} (hP : W.Nonsingular P)
    (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q := by
  rcases Q with ⟨Q⟩
  by_cases hQz : Q z = 0
  · erw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hQ hQz
  · erw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]
    rfl

lemma addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 → F} (hP : W.NonsingularLift P)
    (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P := by
  rcases P with ⟨P⟩
  by_cases hPz : P z = 0
  · erw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
  · erw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]
    rfl

-- DISSOLVED: addMap_of_Y_eq

-- DISSOLVED: addMap_of_Z_ne_zero

lemma nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P)
    (hQ : W.NonsingularLift Q) : W.NonsingularLift <| W.addMap P Q := by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

end Addition

/-! ### Nonsingular rational points -/

variable (W') in

@[ext]
structure Point where
  /-- The point class underlying a nonsingular rational point on `W'`. -/
  {point : PointClass R}
  /-- The nonsingular condition underlying a nonsingular rational point on `W'`. -/
  (nonsingular : W'.NonsingularLift point)

namespace Point

lemma mk_point {P : PointClass R} (h : W'.NonsingularLift P) : (mk h).point = P :=
  rfl

instance instZeroPoint [Nontrivial R] : Zero W'.Point :=
  ⟨⟨nonsingularLift_zero⟩⟩

lemma zero_def [Nontrivial R] : (0 : W'.Point) = ⟨nonsingularLift_zero⟩ :=
  rfl

lemma zero_point [Nontrivial R] : (0 : W'.Point).point = ⟦![1, 1, 0]⟧ :=
  rfl

def fromAffine [Nontrivial R] : W'.toAffine.Point → W'.Point
  | 0 => 0
  | .some h => ⟨(nonsingularLift_some ..).mpr h⟩

-- DISSOLVED: fromAffine_zero

lemma fromAffine_some [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some h) = ⟨(nonsingularLift_some ..).mpr h⟩ :=
  rfl

-- DISSOLVED: fromAffine_ne_zero

def neg (P : W.Point) : W.Point :=
  ⟨nonsingularLift_negMap P.nonsingular⟩

instance instNegPoint : Neg W.Point :=
  ⟨neg⟩

lemma neg_def (P : W.Point) : -P = P.neg :=
  rfl

lemma neg_point (P : W.Point) : (-P).point = W.negMap P.point :=
  rfl

noncomputable def add (P Q : W.Point) : W.Point :=
  ⟨nonsingularLift_addMap P.nonsingular Q.nonsingular⟩

noncomputable instance instAddPoint : Add W.Point :=
  ⟨add⟩

lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl

lemma add_point (P Q : W.Point) : (P + Q).point = W.addMap P.point Q.point :=
  rfl

end Point

section Affine

/-! ### Equivalence with affine coordinates -/

namespace Point

open Classical in

variable (W) in

noncomputable def toAffine (P : Fin 3 → F) : W.toAffine.Point :=
  if hP : W.Nonsingular P ∧ P z ≠ 0 then .some <| (nonsingular_of_Z_ne_zero hP.2).mp hP.1 else 0

lemma toAffine_of_singular {P : Fin 3 → F} (hP : ¬W.Nonsingular P) : toAffine W P = 0 := by
  rw [toAffine, dif_neg <| not_and_of_not_left _ hP]

lemma toAffine_of_Z_eq_zero {P : Fin 3 → F} (hPz : P z = 0) :
    toAffine W P = 0 := by
  rw [toAffine, dif_neg <| not_and_not_right.mpr fun _ => hPz]

-- DISSOLVED: toAffine_zero

-- DISSOLVED: toAffine_of_Z_ne_zero

lemma toAffine_some {X Y : F} (h : W.Nonsingular ![X, Y, 1]) :
    toAffine W ![X, Y, 1] = .some ((nonsingular_some ..).mp h) := by
  simp only [toAffine_of_Z_ne_zero h one_ne_zero, fin3_def_ext, one_pow, div_one]

lemma toAffine_smul (P : Fin 3 → F) {u : F} (hu : IsUnit u) :
    toAffine W (u • P) = toAffine W P := by
  by_cases hP : W.Nonsingular P
  · by_cases hPz : P z = 0
    · rw [toAffine_of_Z_eq_zero <| mul_eq_zero_of_right u hPz, toAffine_of_Z_eq_zero hPz]
    · rw [toAffine_of_Z_ne_zero ((nonsingular_smul P hu).mpr hP) <| mul_ne_zero hu.ne_zero hPz,
        toAffine_of_Z_ne_zero hP hPz, Affine.Point.some.injEq]
      simp only [smul_fin3_ext, mul_pow, mul_div_mul_left _ _ (hu.pow _).ne_zero, and_self]
  · rw [toAffine_of_singular <| hP.comp (nonsingular_smul P hu).mp, toAffine_of_singular hP]

lemma toAffine_of_equiv {P Q : Fin 3 → F} (h : P ≈ Q) : toAffine W P = toAffine W Q := by
  rcases h with ⟨u, rfl⟩
  exact toAffine_smul Q u.isUnit

lemma toAffine_neg {P : Fin 3 → F} (hP : W.Nonsingular P) :
    toAffine W (W.neg P) = -toAffine W P := by
  by_cases hPz : P z = 0
  · rw [neg_of_Z_eq_zero hP hPz,
      toAffine_smul _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg,
      toAffine_zero, toAffine_of_Z_eq_zero hPz, Affine.Point.neg_zero]
  · rw [neg_of_Z_ne_zero hPz, toAffine_smul _ <| Ne.isUnit hPz, toAffine_some <|
        (nonsingular_smul _ <| Ne.isUnit hPz).mp <| neg_of_Z_ne_zero hPz ▸ nonsingular_neg hP,
      toAffine_of_Z_ne_zero hP hPz, Affine.Point.neg_some]

-- DISSOLVED: toAffine_add_of_Z_ne_zero

lemma toAffine_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    toAffine W (W.add P Q) = toAffine W P + toAffine W Q := by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Z_eq_zero hPz, zero_add]
    by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz, toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2,
        toAffine_zero, toAffine_of_Z_eq_zero hQz]
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz,
        toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero_right hQ.left hPz hQz,
        toAffine_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg,
        toAffine_of_Z_eq_zero hQz, add_zero]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 → P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3
      · by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · rw [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| hxy hx,
            toAffine_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx <| hxy hx,
            toAffine_add_of_Z_ne_zero hP hQ hPz hQz hxy]
        · rw [add_of_X_ne hP.left hQ.left hPz hQz hx, toAffine_smul _ <| isUnit_addZ_of_X_ne hx,
            toAffine_add_of_Z_ne_zero hP hQ hPz hQz hxy]
      · rw [_root_.not_imp, not_ne_iff] at hxy
        rw [toAffine_of_Z_ne_zero hP hPz, toAffine_of_Z_ne_zero hQ hQz, Affine.Point.add_of_Y_eq
            ((X_eq_iff hPz hQz).mp hxy.left) ((Y_eq_iff' hPz hQz).mp hxy.right)]
        by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · rw [add_of_Y_eq hPz hQz hxy.left hy hxy.right,
            toAffine_smul _ <| isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, toAffine_zero]
        · rw [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            toAffine_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, toAffine_zero]

noncomputable def toAffineLift (P : W.Point) : W.toAffine.Point :=
  P.point.lift _ fun _ _ => toAffine_of_equiv

lemma toAffineLift_eq {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) :
    toAffineLift ⟨hP⟩ = toAffine W P :=
  rfl

lemma toAffineLift_of_Z_eq_zero {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) (hPz : P z = 0) :
    toAffineLift ⟨hP⟩ = 0 :=
  toAffine_of_Z_eq_zero hPz

lemma toAffineLift_zero : toAffineLift (0 : W.Point) = 0 :=
  toAffine_zero

-- DISSOLVED: toAffineLift_of_Z_ne_zero

lemma toAffineLift_some {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧) :
    toAffineLift ⟨h⟩ = .some ((nonsingular_some ..).mp h) :=
  toAffine_some h

lemma toAffineLift_neg (P : W.Point) : (-P).toAffineLift = -P.toAffineLift := by
  rcases P with @⟨⟨_⟩, hP⟩
  exact toAffine_neg hP

lemma toAffineLift_add (P Q : W.Point) :
    (P + Q).toAffineLift = P.toAffineLift + Q.toAffineLift := by
  rcases P, Q with ⟨@⟨⟨_⟩, hP⟩, @⟨⟨_⟩, hQ⟩⟩
  exact toAffine_add hP hQ

variable (W) in

@[simps]
noncomputable def toAffineAddEquiv : W.Point ≃+ W.toAffine.Point where
  toFun := toAffineLift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, hP⟩
    by_cases hPz : P z = 0
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_eq_zero hPz]
      exact Quotient.eq.mpr <| Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_ne_zero hP hPz]
      exact Quotient.eq.mpr <| Setoid.symm <| equiv_some_of_Z_ne_zero hPz
  right_inv := by
    rintro (_ | _)
    · erw [fromAffine_zero, toAffineLift_zero, Affine.Point.zero_def]
    · rw [fromAffine_some, toAffineLift_some]
  map_add' := toAffineLift_add

end Point

end Affine

section Map

variable {S : Type*} [CommRing S] (f : R →+* S) (P Q : Fin 3 → R)

protected lemma map_smul (u : R) : f ∘ (u • P) = f u • (f ∘ P) := by
  ext i; fin_cases i <;> simp [smul_fin3]

@[simp] lemma map_addZ : addZ (f ∘ P) (f ∘ Q) = f (addZ P Q) := by simp [addZ]

@[simp] lemma map_addX : addX (W'.map f) (f ∘ P) (f ∘ Q) = f (W'.addX P Q) := by
  simp [map_ofNat, addX]

@[simp] lemma map_negAddY : negAddY (W'.map f) (f ∘ P) (f ∘ Q) = f (W'.negAddY P Q) := by
  simp [map_ofNat, negAddY]

@[simp] lemma map_negY : negY (W'.map f) (f ∘ P) = f (W'.negY P) := by simp [negY]

@[simp] protected lemma map_neg : neg (W'.map f) (f ∘ P) = f ∘ W'.neg P := by
  ext i; fin_cases i <;> simp [neg]

@[simp] lemma map_addY : addY (W'.map f) (f ∘ P) (f ∘ Q) = f (W'.addY P Q) := by
  simp [addY, ← comp_fin3]

@[simp] lemma map_addXYZ : addXYZ (W'.map f) (f ∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q := by
  simp_rw [addXYZ, comp_fin3, map_addX, map_addY, map_addZ]

lemma map_polynomial : (W'.map f).toJacobian.polynomial = MvPolynomial.map f W'.polynomial := by
  simp [polynomial]

lemma map_polynomialX : (W'.map f).toJacobian.polynomialX = MvPolynomial.map f W'.polynomialX := by
  simp [polynomialX, map_polynomial, pderiv_map]

lemma map_polynomialY : (W'.map f).toJacobian.polynomialY = MvPolynomial.map f W'.polynomialY := by
  simp [polynomialY, map_polynomial, pderiv_map]

lemma map_polynomialZ : (W'.map f).toJacobian.polynomialZ = MvPolynomial.map f W'.polynomialZ := by
  simp [polynomialZ, map_polynomial, pderiv_map]

@[simp] lemma map_dblZ : dblZ (W'.map f) (f ∘ P) = f (W'.dblZ P) := by simp [dblZ]

@[simp] lemma map_dblU : dblU (W'.map f) (f ∘ P) = f (W'.dblU P) := by
  simp [dblU, map_polynomialX, ← eval₂_id, eval₂_comp_left]

@[simp] lemma map_dblX : dblX (W'.map f) (f ∘ P) = f (W'.dblX P) := by simp [map_ofNat, dblX]

@[simp] lemma map_negDblY : negDblY (W'.map f) (f ∘ P) = f (W'.negDblY P) := by simp [negDblY]

@[simp] lemma map_dblY : dblY (W'.map f) (f ∘ P) = f (W'.dblY P) := by simp [dblY, ← comp_fin3]

@[simp] lemma map_dblXYZ : dblXYZ (W'.map f) (f ∘ P) = f ∘ dblXYZ W' P := by
  simp_rw [dblXYZ, comp_fin3, map_dblX, map_dblY, map_dblZ]

end Map

end WeierstrassCurve.Jacobian

abbrev WeierstrassCurve.Affine.Point.toJacobian {R : Type u} [CommRing R]
    [Nontrivial R] {W : Affine R} (P : W.Point) : W.toJacobian.Point :=
  Jacobian.Point.fromAffine P

set_option linter.style.longFile 1700
