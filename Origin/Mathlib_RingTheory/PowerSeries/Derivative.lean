/-
Extracted from RingTheory/PowerSeries/Derivative.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definitions

In this file we define an operation `derivative` (formal differentiation)
on the ring of formal power series in one variable (over an arbitrary commutative semiring).

Under suitable assumptions, we prove that two power series are equal if their derivatives
are equal and their constant terms are equal. This will give us a simple tool for proving
power series identities. For example, one can easily prove the power series identity
$\exp ( \log (1+X)) = 1+X$ by differentiating twice.

## Main Definition

- `PowerSeries.derivative R : Derivation R R⟦X⟧ R⟦X⟧` the formal derivative operation.
  This is abbreviated `d⁄dX R`.
-/

namespace PowerSeries

open Polynomial Derivation Nat

section CommutativeSemiring

variable {R} [CommSemiring R]

noncomputable def derivativeFun (f : R⟦X⟧) : R⟦X⟧ := mk fun n ↦ coeff (n + 1) f * (n + 1)

theorem coeff_derivativeFun (f : R⟦X⟧) (n : ℕ) :
    coeff n f.derivativeFun = coeff (n + 1) f * (n + 1) := by
  rw [derivativeFun, coeff_mk]

theorem derivativeFun_coe (f : R[X]) : (f : R⟦X⟧).derivativeFun = derivative f := by
  ext
  rw [coeff_derivativeFun, coeff_coe, coeff_coe, coeff_derivative]

theorem derivativeFun_add (f g : R⟦X⟧) :
    derivativeFun (f + g) = derivativeFun f + derivativeFun g := by
  ext
  rw [coeff_derivativeFun, map_add, map_add, coeff_derivativeFun,
    coeff_derivativeFun, add_mul]

theorem derivativeFun_C (r : R) : derivativeFun (C r) = 0 := by
  ext n
  -- Note that `map_zero` didn't get picked up, apparently due to a missing `FunLike.coe`
  rw [coeff_derivativeFun, coeff_succ_C, zero_mul, (coeff n).map_zero]

theorem trunc_derivativeFun (f : R⟦X⟧) (n : ℕ) :
    trunc n f.derivativeFun = derivative (trunc (n + 1) f) := by
  ext d
  rw [coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_derivativeFun, coeff_derivative, coeff_trunc, if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [coeff_derivative, coeff_trunc, if_neg this, zero_mul]

private theorem derivativeFun_coe_mul_coe (f g : R[X]) : derivativeFun (f * g : R⟦X⟧) =
    f * derivative g + g * derivative f := by
  rw [← coe_mul, derivativeFun_coe, derivative_mul,
    add_comm, mul_comm _ g, ← coe_mul, ← coe_mul, Polynomial.coe_add]

theorem derivativeFun_mul (f g : R⟦X⟧) :
    derivativeFun (f * g) = f • g.derivativeFun + g • f.derivativeFun := by
  ext n
  have h₁ : n < n + 1 := lt_succ_self n
  have h₂ : n < n + 1 + 1 := Nat.lt_add_right _ h₁
  rw [coeff_derivativeFun, map_add, coeff_mul_eq_coeff_trunc_mul_trunc _ _ (lt_succ_self _),
    smul_eq_mul, smul_eq_mul, coeff_mul_eq_coeff_trunc_mul_trunc₂ g f.derivativeFun h₂ h₁,
    coeff_mul_eq_coeff_trunc_mul_trunc₂ f g.derivativeFun h₂ h₁, trunc_derivativeFun,
    trunc_derivativeFun, ← map_add, ← derivativeFun_coe_mul_coe, coeff_derivativeFun]

theorem derivativeFun_one : derivativeFun (1 : R⟦X⟧) = 0 := by
  rw [← map_one C, derivativeFun_C (1 : R)]

theorem derivativeFun_smul (r : R) (f : R⟦X⟧) : derivativeFun (r • f) = r • derivativeFun f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, derivativeFun_mul, derivativeFun_C, smul_zero, add_zero,
    smul_eq_mul]

variable (R)

noncomputable def derivative : Derivation R R⟦X⟧ R⟦X⟧ where
  toFun := derivativeFun
  map_add' := derivativeFun_add
  map_smul' := derivativeFun_smul
  map_one_eq_zero' := derivativeFun_one
  leibniz' := derivativeFun_mul

scoped notation "d⁄dX" => derivative

variable {R}
