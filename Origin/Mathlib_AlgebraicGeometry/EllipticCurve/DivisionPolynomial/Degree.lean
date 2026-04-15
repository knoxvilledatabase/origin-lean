/-
Extracted from AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean
Genuine: 24 of 58 | Dissolved: 34 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Division polynomials of Weierstrass curves

This file computes the leading terms of certain polynomials associated to division polynomials of
Weierstrass curves defined in `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.

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

@[simp]
lemma coeff_Ψ₂Sq : W.Ψ₂Sq.coeff 3 = 4 := by
  rw [Ψ₂Sq]
  compute_degree!

-- DISSOLVED: coeff_Ψ₂Sq_ne_zero

-- DISSOLVED: natDegree_Ψ₂Sq

-- DISSOLVED: natDegree_Ψ₂Sq_pos

-- DISSOLVED: leadingCoeff_Ψ₂Sq

-- DISSOLVED: Ψ₂Sq_ne_zero

end Ψ₂Sq

section Ψ₃

lemma natDegree_Ψ₃_le : W.Ψ₃.natDegree ≤ 4 := by
  rw [Ψ₃]
  compute_degree

@[simp]
lemma coeff_Ψ₃ : W.Ψ₃.coeff 4 = 3 := by
  rw [Ψ₃]
  compute_degree!

-- DISSOLVED: coeff_Ψ₃_ne_zero

-- DISSOLVED: natDegree_Ψ₃

-- DISSOLVED: natDegree_Ψ₃_pos

-- DISSOLVED: leadingCoeff_Ψ₃

-- DISSOLVED: Ψ₃_ne_zero

end Ψ₃

section preΨ₄

lemma natDegree_preΨ₄_le : W.preΨ₄.natDegree ≤ 6 := by
  rw [preΨ₄]
  compute_degree

@[simp]
lemma coeff_preΨ₄ : W.preΨ₄.coeff 6 = 2 := by
  rw [preΨ₄]
  compute_degree!

-- DISSOLVED: coeff_preΨ₄_ne_zero

-- DISSOLVED: natDegree_preΨ₄

-- DISSOLVED: natDegree_preΨ₄_pos

-- DISSOLVED: leadingCoeff_preΨ₄

-- DISSOLVED: preΨ₄_ne_zero

end preΨ₄

section preΨ'

private def expDegree (n : ℕ) : ℕ :=
  (n ^ 2 - if Even n then 4 else 1) / 2

-- DISSOLVED: expDegree_cast

private lemma expDegree_rec (m : ℕ) :
    (expDegree (2 * (m + 3)) = 2 * expDegree (m + 2) + expDegree (m + 3) + expDegree (m + 5) ∧
    expDegree (2 * (m + 3)) = expDegree (m + 1) + expDegree (m + 3) + 2 * expDegree (m + 4)) ∧
    (expDegree (2 * (m + 2) + 1) =
      expDegree (m + 4) + 3 * expDegree (m + 2) + (if Even m then 2 * 3 else 0) ∧
    expDegree (2 * (m + 2) + 1) =
      expDegree (m + 1) + 3 * expDegree (m + 3) + (if Even m then 0 else 2 * 3)) := by
  push_cast [← @Nat.cast_inj ℤ, ← mul_left_cancel_iff_of_pos (b := (expDegree _ : ℤ)) two_pos,
    mul_add, mul_left_comm (2 : ℤ)]
  repeat rw [expDegree_cast <| by omega]
  push_cast [Nat.even_add_one, ite_not, even_two_mul]
  constructor <;> constructor <;> split_ifs <;> ring1

private def expCoeff (n : ℕ) : ℤ :=
  if Even n then n / 2 else n

private lemma expCoeff_cast (n : ℕ) : (expCoeff n : ℚ) = if Even n then (n / 2 : ℚ) else n := by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]

private lemma expCoeff_rec (m : ℕ) :
    (expCoeff (2 * (m + 3)) =
      expCoeff (m + 2) ^ 2 * expCoeff (m + 3) * expCoeff (m + 5) -
        expCoeff (m + 1) * expCoeff (m + 3) * expCoeff (m + 4) ^ 2) ∧
    (expCoeff (2 * (m + 2) + 1) =
      expCoeff (m + 4) * expCoeff (m + 2) ^ 3 * (if Even m then 4 ^ 2 else 1) -
        expCoeff (m + 1) * expCoeff (m + 3) ^ 3 * (if Even m then 1 else 4 ^ 2)) := by
  push_cast [← @Int.cast_inj ℚ, expCoeff_cast, even_two_mul, m.not_even_two_mul_add_one,
    Nat.even_add_one, ite_not]
  constructor <;> split_ifs <;> ring1

private lemma natDegree_coeff_preΨ' (n : ℕ) :
    (W.preΨ' n).natDegree ≤ expDegree n ∧ (W.preΨ' n).coeff (expDegree n) = expCoeff n := by
  let dm {m n p q} : _ → _ → (p * q : R[X]).natDegree ≤ m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ → (p ^ n : R[X]).natDegree ≤ n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ → _ → (p * q : R[X]).coeff (m + n) = _ := coeff_mul_of_natDegree_le
  let cp {m n p} : _ → (p ^ m : R[X]).coeff (m * n) = _ := coeff_pow_of_natDegree_le
  induction n using normEDSRec with
  | zero => simpa only [preΨ'_zero] using ⟨by rfl, Int.cast_zero.symm⟩
  | one => simpa only [preΨ'_one] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | two => simpa only [preΨ'_two] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | three => simpa only [preΨ'_three] using ⟨W.natDegree_Ψ₃_le, W.coeff_Ψ₃ ▸ Int.cast_three.symm⟩
  | four => simpa only [preΨ'_four] using ⟨W.natDegree_preΨ₄_le, W.coeff_preΨ₄ ▸ Int.cast_two.symm⟩
  | even m h₁ h₂ h₃ h₄ h₅ =>
    constructor
    · nth_rw 1 [preΨ'_even, ← max_self <| expDegree _, (expDegree_rec m).1.1, (expDegree_rec m).1.2]
      exact natDegree_sub_le_of_le (dm (dm (dp h₂.1) h₃.1) h₅.1) (dm (dm h₁.1 h₃.1) (dp h₄.1))
    · nth_rw 1 [preΨ'_even, coeff_sub, (expDegree_rec m).1.1, cm (dm (dp h₂.1) h₃.1) h₅.1,
        cm (dp h₂.1) h₃.1, cp h₂.1, h₂.2, h₃.2, h₅.2, (expDegree_rec m).1.2,
        cm (dm h₁.1 h₃.1) (dp h₄.1), cm h₁.1 h₃.1, h₁.2, cp h₄.1, h₃.2, h₄.2, (expCoeff_rec m).1]
      norm_cast
  | odd m h₁ h₂ h₃ h₄ =>
    rw [preΨ'_odd]
    constructor
    · nth_rw 1 [← max_self <| expDegree _, (expDegree_rec m).2.1, (expDegree_rec m).2.2]
      refine natDegree_sub_le_of_le (dm (dm h₄.1 (dp h₂.1)) ?_) (dm (dm h₁.1 (dp h₃.1)) ?_)
      all_goals split_ifs <;>
        simp only [apply_ite natDegree, natDegree_one.le, dp W.natDegree_Ψ₂Sq_le]
    · nth_rw 1 [coeff_sub, (expDegree_rec m).2.1, cm (dm h₄.1 (dp h₂.1)), cm h₄.1 (dp h₂.1),
        h₄.2, cp h₂.1, h₂.2, apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq_le, coeff_Ψ₂Sq, coeff_one_zero,
        (expDegree_rec m).2.2, cm (dm h₁.1 (dp h₃.1)), cm h₁.1 (dp h₃.1), h₁.2, cp h₃.1, h₃.2,
        apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq_le, coeff_one_zero, coeff_Ψ₂Sq, (expCoeff_rec m).2]
      · norm_cast
      all_goals split_ifs <;>
        simp only [apply_ite natDegree, natDegree_one.le, dp W.natDegree_Ψ₂Sq_le]

lemma natDegree_preΨ'_le (n : ℕ) : (W.preΨ' n).natDegree ≤ (n ^ 2 - if Even n then 4 else 1) / 2 :=
  (W.natDegree_coeff_preΨ' n).left

@[simp]
lemma coeff_preΨ' (n : ℕ) : (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) =
    if Even n then n / 2 else n := by
  convert (W.natDegree_coeff_preΨ' n).right using 1
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]

-- DISSOLVED: coeff_preΨ'_ne_zero

-- DISSOLVED: natDegree_preΨ'

-- DISSOLVED: natDegree_preΨ'_pos

-- DISSOLVED: leadingCoeff_preΨ'

-- DISSOLVED: preΨ'_ne_zero

end preΨ'

section preΨ

lemma natDegree_preΨ_le (n : ℤ) : (W.preΨ n).natDegree ≤
    (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.natDegree_preΨ'_le n
  | neg ih => simp only [preΨ_neg, natDegree_neg, Int.natAbs_neg, even_neg, ih]

@[simp]
lemma coeff_preΨ (n : ℤ) : (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) =
    if Even n then n / 2 else n := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.coeff_preΨ' n
  | neg ih n =>
    simp only [preΨ_neg, coeff_neg, Int.natAbs_neg, even_neg]
    rcases ih n, n.even_or_odd' with ⟨ih, ⟨n, rfl | rfl⟩⟩ <;>
      push_cast [even_two_mul, Int.not_even_two_mul_add_one, Int.neg_ediv_of_dvd ⟨n, rfl⟩] at * <;>
      rw [ih]

-- DISSOLVED: coeff_preΨ_ne_zero

-- DISSOLVED: natDegree_preΨ

-- DISSOLVED: natDegree_preΨ_pos

-- DISSOLVED: leadingCoeff_preΨ

-- DISSOLVED: preΨ_ne_zero

end preΨ

section ΨSq

private lemma natDegree_coeff_ΨSq_ofNat (n : ℕ) :
    (W.ΨSq n).natDegree ≤ n ^ 2 - 1 ∧ (W.ΨSq n).coeff (n ^ 2 - 1) = (n ^ 2 : ℤ) := by
  let dp {m n p} : _ → (p ^ n : R[X]).natDegree ≤ n * m := natDegree_pow_le_of_le n
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | n
  · simp
  have hd : (n + 1) ^ 2 - 1 = 2 * expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj ℤ, add_sq, expDegree_cast (by omega : n + 1 ≠ 0)]
    split_ifs <;> ring1
  have hc : (n + 1 : ℕ) ^ 2 = expCoeff (n + 1) ^ 2 * if Even (n + 1) then 4 else 1 := by
    push_cast [← @Int.cast_inj ℚ, expCoeff_cast]
    split_ifs <;> ring1
  rw [ΨSq_ofNat, hd]
  constructor
  · refine natDegree_mul_le_of_le (dp h.1) ?_
    split_ifs <;> simp only [apply_ite natDegree, natDegree_one.le, W.natDegree_Ψ₂Sq_le]
  · rw [coeff_mul_of_natDegree_le (dp h.1), coeff_pow_of_natDegree_le h.1, h.2, apply_ite₂ coeff,
      coeff_Ψ₂Sq, coeff_one_zero, hc]
    · norm_cast
    split_ifs <;> simp only [apply_ite natDegree, natDegree_one.le, W.natDegree_Ψ₂Sq_le]

lemma natDegree_ΨSq_le (n : ℤ) : (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_ΨSq_ofNat n).left
  | neg ih => simp only [ΨSq_neg, Int.natAbs_neg, ih]

@[simp]
lemma coeff_ΨSq (n : ℤ) : (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2 := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast (W.natDegree_coeff_ΨSq_ofNat n).right
  | neg ih => simp_rw [ΨSq_neg, Int.natAbs_neg, ← Int.cast_pow, neg_sq, Int.cast_pow, ih]

-- DISSOLVED: coeff_ΨSq_ne_zero

-- DISSOLVED: natDegree_ΨSq

-- DISSOLVED: natDegree_ΨSq_pos

-- DISSOLVED: leadingCoeff_ΨSq

-- DISSOLVED: ΨSq_ne_zero

end ΨSq

section Φ

private lemma natDegree_coeff_Φ_ofNat (n : ℕ) :
    (W.Φ n).natDegree ≤ n ^ 2 ∧ (W.Φ n).coeff (n ^ 2) = 1 := by
  let dm {m n p q} : _ → _ → (p * q : R[X]).natDegree ≤ m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ → (p ^ n : R[X]).natDegree ≤ n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ → _ → (p * q : R[X]).coeff (m + n) = _ := coeff_mul_of_natDegree_le
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | _ | n
  · simp
  · simp [natDegree_X_le]
  have hd : (n + 1 + 1) ^ 2 = 1 + 2 * expDegree (n + 2) + if Even (n + 1) then 0 else 3 := by
    push_cast [← @Nat.cast_inj ℤ, expDegree_cast (by omega : n + 2 ≠ 0), Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hd' : (n + 1 + 1) ^ 2 =
      expDegree (n + 3) + expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj ℤ, ← mul_left_cancel_iff_of_pos (b := (_ ^ 2 : ℤ)) two_pos, mul_add,
      expDegree_cast (by omega : n + 3 ≠ 0), expDegree_cast (by omega : n + 1 ≠ 0),
      Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hc : (1 : ℤ) = 1 * expCoeff (n + 2) ^ 2 * (if Even (n + 1) then 1 else 4) -
      expCoeff (n + 3) * expCoeff (n + 1) * (if Even (n + 1) then 4 else 1) := by
    push_cast [← @Int.cast_inj ℚ, expCoeff_cast, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  rw [Nat.cast_add, Nat.cast_one, Φ_ofNat]
  constructor
  · nth_rw 1 [← max_self <| (_ + _) ^ 2, hd, hd']
    refine natDegree_sub_le_of_le (dm (dm natDegree_X_le (dp h.1)) ?_) (dm (dm h.1 h.1) ?_)
    all_goals split_ifs <;> simp only [apply_ite natDegree, natDegree_one.le, W.natDegree_Ψ₂Sq_le]
  · nth_rw 1 [coeff_sub, hd, hd', cm (dm natDegree_X_le (dp h.1)), cm natDegree_X_le (dp h.1),
      coeff_X_one, coeff_pow_of_natDegree_le h.1, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq,
      cm (dm h.1 h.1), cm h.1 h.1, h.2, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq]
    conv_rhs => rw [← Int.cast_one, hc]
    · norm_cast
    all_goals split_ifs <;> simp only [apply_ite natDegree, natDegree_one.le, W.natDegree_Ψ₂Sq_le]

lemma natDegree_Φ_le (n : ℤ) : (W.Φ n).natDegree ≤ n.natAbs ^ 2 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).left
  | neg ih => simp only [Φ_neg, Int.natAbs_neg, ih]

@[simp]
lemma coeff_Φ (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) = 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).right
  | neg ih => simp only [Φ_neg, Int.natAbs_neg, ih]

-- DISSOLVED: coeff_Φ_ne_zero

@[simp]
lemma natDegree_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).natDegree = n.natAbs ^ 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_Φ_le n) <| W.coeff_Φ_ne_zero n

-- DISSOLVED: natDegree_Φ_pos

@[simp]
lemma leadingCoeff_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).leadingCoeff = 1 := by
  rw [leadingCoeff, natDegree_Φ, coeff_Φ]

-- DISSOLVED: Φ_ne_zero

end Φ

end WeierstrassCurve
