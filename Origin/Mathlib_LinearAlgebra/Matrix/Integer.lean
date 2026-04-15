/-
Extracted from LinearAlgebra/Matrix/Integer.lean
Genuine: 9 of 10 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas on integer matrices

Here we collect some results about matrices over `ℚ` and `ℤ`.

## Main definitions and results

* `Matrix.num`, `Matrix.den`: express a rational matrix `A` as the quotient of an integer matrix
  by a (non-zero) natural.

## TODO

Consider generalizing these constructions to matrices over localizations of rings (or semirings).
-/

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-!
## Casts

These results are useful shortcuts because the canonical casting maps out of `ℕ`, `ℤ`, and `ℚ` to
suitable types are bare functions, not ring homs, so we cannot apply `Matrix.map_mul` directly to
them.
-/

lemma map_mul_natCast {α : Type*} [NonAssocSemiring α] (A B : Matrix n n ℕ) :
    map (A * B) ((↑) : ℕ → α) = map A (↑) * map B (↑) :=
  Matrix.map_mul (f := Nat.castRingHom α)

lemma map_mul_intCast {α : Type*} [NonAssocRing α] (A B : Matrix n n ℤ) :
    map (A * B) ((↑) : ℤ → α) = map A (↑) * map B (↑) :=
  Matrix.map_mul (f := Int.castRingHom α)

lemma map_mul_ratCast {α : Type*} [DivisionRing α] [CharZero α] (A B : Matrix n n ℚ) :
    map (A * B) ((↑) : ℚ → α) = map A (↑) * map B (↑) :=
  Matrix.map_mul (f := Rat.castHom α)

/-!
## Denominator of a rational matrix
-/

protected def den (A : Matrix m n ℚ) : ℕ := Finset.univ.lcm (fun P : m × n ↦ (A P.1 P.2).den)

protected def num (A : Matrix m n ℚ) : Matrix m n ℤ := ((A.den : ℚ) • A).map Rat.num

-- DISSOLVED: den_ne_zero

lemma num_eq_zero_iff (A : Matrix m n ℚ) : A.num = 0 ↔ A = 0 := by
  simp [Matrix.num, ← ext_iff, A.den_ne_zero]

lemma den_dvd_iff {A : Matrix m n ℚ} {r : ℕ} :
    A.den ∣ r ↔ ∀ i j, (A i j).den ∣ r := by
  simp [Matrix.den]

lemma num_div_den (A : Matrix m n ℚ) (i : m) (j : n) :
    A.num i j / A.den = A i j := by
  obtain ⟨k, hk⟩ := den_dvd_iff.mp (dvd_refl A.den) i j
  rw [Matrix.num, map_apply, smul_apply, smul_eq_mul, mul_comm,
    div_eq_iff <| Nat.cast_ne_zero.mpr A.den_ne_zero, hk, Nat.cast_mul, ← mul_assoc,
    Rat.mul_den_eq_num, ← Int.cast_natCast k, ← Int.cast_mul, Rat.num_intCast]

lemma inv_denom_smul_num (A : Matrix m n ℚ) :
    (A.den⁻¹ : ℚ) • A.num.map (↑) = A := by
  ext
  simp [← Matrix.num_div_den A, div_eq_inv_mul]
