/-
Extracted from Algebra/Polynomial/Derivative.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The derivative map on polynomials

## Main definitions
* `Polynomial.derivative`: The formal derivative of polynomials, expressed as a linear map.
* `Polynomial.derivativeFinsupp`: Iterated derivatives as a finite support function.

-/

noncomputable section

open Finset

open Polynomial

open scoped Nat

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

section Derivative

section Semiring

variable [Semiring R]

def derivative : R[X] →ₗ[R] R[X] where
  toFun p := p.sum fun n a => C (a * n) * X ^ (n - 1)
  map_add' p q := by
    rw [sum_add_index] <;>
      simp only [add_mul, forall_const, map_add, zero_mul, map_zero]
  map_smul' a p := by
    dsimp; rw [sum_smul_index] <;>
      simp only [mul_sum, ← C_mul', mul_assoc, map_mul, forall_const, zero_mul, map_zero, sum]

theorem coeff_derivative (p : R[X]) (n : ℕ) :
    coeff (derivative p) n = coeff p (n + 1) * (n + 1) := by
  rw [derivative_apply]
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul]
  rw [sum, Finset.sum_eq_single (n + 1)]
  · simp only [Nat.add_succ_sub_one, add_zero, mul_one, if_true]; norm_cast
  · intro b
    cases b
    · intros
      rw [Nat.cast_zero, mul_zero, zero_mul]
    · intro _ H
      rw [Nat.add_one_sub_one, if_neg (mt (congr_arg Nat.succ) H.symm), mul_zero]
  · simp_all
