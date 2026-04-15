/-
Extracted from RingTheory/Polynomial/Chebyshev.lean
Genuine: 35 of 39 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

/-!
# Chebyshev polynomials

The Chebyshev polynomials are families of polynomials indexed by `ℤ`,
with integral coefficients.

## Main definitions

* `Polynomial.Chebyshev.T`: the Chebyshev polynomials of the first kind.
* `Polynomial.Chebyshev.U`: the Chebyshev polynomials of the second kind.

## Main statements

* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.
* `Polynomial.Chebyshev.mul_T`, twice the product of the `m`-th and `k`-th Chebyshev polynomials of
  the first kind is the sum of the `m + k`-th and `m - k`-th Chebyshev polynomials of the first
  kind.
* `Polynomial.Chebyshev.T_mul`, the `(m * n)`-th Chebyshev polynomial of the first kind is the
  composition of the `m`-th and `n`-th Chebyshev polynomials of the first kind.

## Implementation details

Since Chebyshev polynomials have interesting behaviour over the complex numbers and modulo `p`,
we define them to have coefficients in an arbitrary commutative ring, even though
technically `ℤ` would suffice.
The benefit of allowing arbitrary coefficient rings, is that the statements afterwards are clean,
and do not have `map (Int.castRingHom R)` interfering all the time.

## References

[Lionel Ponton, _Roots of the Chebyshev polynomials: A purely algebraic approach_]
[ponton2020chebyshev]

## TODO

* Redefine and/or relate the definition of Chebyshev polynomials to `LinearRecurrence`.
* Add explicit formula involving square roots for Chebyshev polynomials
* Compute zeroes and extrema of Chebyshev polynomials.
* Prove that the roots of the Chebyshev polynomials (except 0) are irrational.
* Prove minimax properties of Chebyshev polynomials.
-/

namespace Polynomial.Chebyshev

open Polynomial

variable (R S : Type*) [CommRing R] [CommRing S]

@[semireducible] noncomputable def T : ℤ → R[X]
  | 0 => 1
  | 1 => X
  | (n : ℕ) + 2 => 2 * X * T (n + 1) - T n
  | -((n : ℕ) + 1) => 2 * X * T (-n) - T (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)

@[elab_as_elim]
protected theorem induct (motive : ℤ → Prop)
    (zero : motive 0)
    (one : motive 1)
    (add_two : ∀ (n : ℕ), motive (↑n + 1) → motive ↑n → motive (↑n + 2))
    (neg_add_one : ∀ (n : ℕ), motive (-↑n) → motive (-↑n + 1) → motive (-↑n - 1)) :
    ∀ (a : ℤ), motive a :=
  T.induct Unit motive zero one add_two fun n hn hnm => by
    simpa only [Int.negSucc_eq, neg_add] using neg_add_one n hn hnm

@[simp]
theorem T_add_two : ∀ n, T R (n + 2) = 2 * X * T R (n + 1) - T R n
  | (k : ℕ) => T.eq_3 R k
  | -(k + 1 : ℕ) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) T.eq_4 R k

theorem T_add_one (n : ℤ) : T R (n + 1) = 2 * X * T R n - T R (n - 1) := by
  linear_combination (norm := ring_nf) T_add_two R (n - 1)

theorem T_sub_two (n : ℤ) : T R (n - 2) = 2 * X * T R (n - 1) - T R n := by
  linear_combination (norm := ring_nf) T_add_two R (n - 2)

theorem T_sub_one (n : ℤ) : T R (n - 1) = 2 * X * T R n - T R (n + 1) := by
  linear_combination (norm := ring_nf) T_add_two R (n - 1)

theorem T_eq (n : ℤ) : T R n = 2 * X * T R (n - 1) - T R (n - 2) := by
  linear_combination (norm := ring_nf) T_add_two R (n - 2)

@[simp]
theorem T_zero : T R 0 = 1 := rfl

@[simp]
theorem T_one : T R 1 = X := rfl

theorem T_neg_one : T R (-1) = X := (by ring : 2 * X * 1 - X = X)

theorem T_two : T R 2 = 2 * X ^ 2 - 1 := by
  simpa [pow_two, mul_assoc] using T_add_two R 0

@[simp]
theorem T_neg (n : ℤ) : T R (-n) = T R n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => rfl
  | one => show 2 * X * 1 - X = X; ring
  | add_two n ih1 ih2 =>
    have h₁ := T_add_two R n
    have h₂ := T_sub_two R (-n)
    linear_combination (norm := ring_nf) (2 * (X : R[X])) * ih1 - ih2 - h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := T_add_one R n
    have h₂ := T_sub_one R (-n)
    linear_combination (norm := ring_nf) (2 * (X : R[X])) * ih1 - ih2 + h₁ - h₂

theorem T_natAbs (n : ℤ) : T R n.natAbs = T R n := by
  obtain h | h := Int.natAbs_eq n <;> nth_rw 2 [h]; simp

theorem T_neg_two : T R (-2) = 2 * X ^ 2 - 1 := by simp [T_two]

@[semireducible] noncomputable def U : ℤ → R[X]
  | 0 => 1
  | 1 => 2 * X
  | (n : ℕ) + 2 => 2 * X * U (n + 1) - U n
  | -((n : ℕ) + 1) => 2 * X * U (-n) - U (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)

@[simp]
theorem U_add_two : ∀ n, U R (n + 2) = 2 * X * U R (n + 1) - U R n
  | (k : ℕ) => U.eq_3 R k
  | -(k + 1 : ℕ) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) U.eq_4 R k

theorem U_add_one (n : ℤ) : U R (n + 1) = 2 * X * U R n - U R (n - 1) := by
  linear_combination (norm := ring_nf) U_add_two R (n - 1)

theorem U_sub_two (n : ℤ) : U R (n - 2) = 2 * X * U R (n - 1) - U R n := by
  linear_combination (norm := ring_nf) U_add_two R (n - 2)

theorem U_sub_one (n : ℤ) : U R (n - 1) = 2 * X * U R n - U R (n + 1) := by
  linear_combination (norm := ring_nf) U_add_two R (n - 1)

theorem U_eq (n : ℤ) : U R n = 2 * X * U R (n - 1) - U R (n - 2) := by
  linear_combination (norm := ring_nf) U_add_two R (n - 2)

@[simp]
theorem U_zero : U R 0 = 1 := rfl

@[simp]
theorem U_one : U R 1 = 2 * X := rfl

@[simp]
theorem U_neg_one : U R (-1) = 0 := by simpa using U_sub_one R 0

theorem U_two : U R 2 = 4 * X ^ 2 - 1 := by
  have := U_add_two R 0
  simp only [zero_add, U_one, U_zero] at this
  linear_combination this

@[simp]
theorem U_neg_two : U R (-2) = -1 := by
  simpa [zero_sub, Int.reduceNeg, U_neg_one, mul_zero, U_zero] using U_sub_two R 0

theorem U_neg_sub_one (n : ℤ) : U R (-n - 1) = -U R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := U_add_one R n
    have h₂ := U_sub_two R (-n - 1)
    linear_combination (norm := ring_nf) 2 * (X : R[X]) * ih1 - ih2 + h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := U_eq R n
    have h₂ := U_sub_two R (-n)
    linear_combination (norm := ring_nf) 2 * (X : R[X]) * ih1 - ih2 + h₁ + h₂

theorem U_neg (n : ℤ) : U R (-n) = -U R (n - 2) := by simpa [sub_sub] using U_neg_sub_one R (n - 1)

@[simp]
theorem U_neg_sub_two (n : ℤ) : U R (-n - 2) = -U R n := by
  simpa [sub_eq_add_neg, add_comm] using U_neg R (n + 2)

theorem U_eq_X_mul_U_add_T (n : ℤ) : U R (n + 1) = X * U R n + T R (n + 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => simp [U_two, T_two]; ring
  | add_two n ih1 ih2 =>
    have h₁ := U_add_two R (n + 1)
    have h₂ := U_add_two R n
    have h₃ := T_add_two R (n + 1)
    linear_combination (norm := ring_nf) -h₃ - (X : R[X]) * h₂ + h₁ + 2 * (X : R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := U_add_two R (-n - 1)
    have h₂ := U_add_two R (-n)
    have h₃ := T_add_two R (-n)
    linear_combination (norm := ring_nf) -h₃ + h₂ - (X : R[X]) * h₁ - ih2 + 2 * (X : R[X]) * ih1

theorem T_eq_U_sub_X_mul_U (n : ℤ) : T R n = U R n - X * U R (n - 1) := by
  linear_combination (norm := ring_nf) - U_eq_X_mul_U_add_T R (n - 1)

theorem T_eq_X_mul_T_sub_pol_U (n : ℤ) : T R (n + 2) = X * T R (n + 1) - (1 - X ^ 2) * U R n := by
  have h₁ := U_eq_X_mul_U_add_T R n
  have h₂ := U_eq_X_mul_U_add_T R (n + 1)
  have h₃ := U_add_two R n
  linear_combination (norm := ring_nf) h₃ - h₂ + (X : R[X]) * h₁

theorem one_sub_X_sq_mul_U_eq_pol_in_T (n : ℤ) :
    (1 - X ^ 2) * U R n = X * T R (n + 1) - T R (n + 2) := by
  linear_combination T_eq_X_mul_T_sub_pol_U R n

variable {R S}

@[simp]
theorem map_T (f : R →+* S) (n : ℤ) : map f (T R n) = T S n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [T_add_two, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X,
      ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [T_sub_one, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]

@[simp]
theorem map_U (f : R →+* S) (n : ℤ) : map f (U R n) = U S n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [U_add_two, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [U_sub_one, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]

theorem T_derivative_eq_U (n : ℤ) : derivative (T R n) = n * U R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one =>
    simp [T_two, U_one, derivative_sub, derivative_one, derivative_mul, derivative_X_pow, add_mul]
  | add_two n ih1 ih2 =>
    have h₁ := congr_arg derivative (T_add_two R n)
    have h₂ := U_sub_one R n
    have h₃ := T_eq_U_sub_X_mul_U R (n + 1)
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      h₁ - ih2 + 2 * (X : R[X]) * ih1 + 2 * h₃ - n * h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := congr_arg derivative (T_sub_one R (-n))
    have h₂ := U_sub_two R (-n)
    have h₃ := T_eq_U_sub_X_mul_U R (-n)
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      -ih2 + 2 * (X : R[X]) * ih1 + h₁ + 2 * h₃ + (n + 1) * h₂

theorem one_sub_X_sq_mul_derivative_T_eq_poly_in_T (n : ℤ) :
    (1 - X ^ 2) * derivative (T R (n + 1)) = (n + 1 : R[X]) * (T R n - X * T R (n + 1)) := by
  have H₁ := one_sub_X_sq_mul_U_eq_pol_in_T R n
  have H₂ := T_derivative_eq_U (R := R) (n + 1)
  have h₁ := T_add_two R n
  linear_combination (norm := (push_cast; ring_nf))
    (-n - 1) * h₁ + (-(X : R[X]) ^ 2 + 1) * H₂ + (n + 1) * H₁

theorem add_one_mul_T_eq_poly_in_U (n : ℤ) :
    ((n : R[X]) + 1) * T R (n + 1) = X * U R n - (1 - X ^ 2) * derivative (U R n) := by
  have h₁ := congr_arg derivative <| T_eq_X_mul_T_sub_pol_U R n
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
    T_derivative_eq_U, C_eq_natCast] at h₁
  have h₂ := T_eq_U_sub_X_mul_U R (n + 1)
  linear_combination (norm := (push_cast; ring_nf))
    h₁ + (n + 2) * h₂

variable (R)

theorem mul_T (m k : ℤ) : 2 * T R m * T R k = T R (m + k) + T R (m - k) := by
  induction k using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => rw [T_add_one, T_one]; ring
  | add_two k ih1 ih2 =>
    have h₁ := T_add_two R (m + k)
    have h₂ := T_sub_two R (m - k)
    have h₃ := T_add_two R k
    linear_combination (norm := ring_nf) 2 * T R m * h₃ - h₂ - h₁ - ih2 + 2 * (X : R[X]) * ih1
  | neg_add_one k ih1 ih2 =>
    have h₁ := T_add_two R (m + (-k - 1))
    have h₂ := T_sub_two R (m - (-k - 1))
    have h₃ := T_add_two R (-k - 1)
    linear_combination (norm := ring_nf) 2 * T R m * h₃ - h₂ - h₁ - ih2 + 2 * (X : R[X]) * ih1

theorem T_mul (m n : ℤ) : T R (m * n) = (T R m).comp (T R n) := by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two m ih1 ih2 =>
    have h₁ := mul_T R ((m + 1) * n) n
    have h₂ := congr_arg (comp · (T R n)) <| T_add_two R m
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + 2 * T R n * ih1
  | neg_add_one m ih1 ih2 =>
    have h₁ := mul_T R ((-m) * n) n
    have h₂ := congr_arg (comp · (T R n)) <| T_add_two R (-m - 1)
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + 2 * T R n * ih1

end Polynomial.Chebyshev
