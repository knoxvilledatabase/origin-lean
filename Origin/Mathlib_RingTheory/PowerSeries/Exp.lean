/-
Extracted from RingTheory/PowerSeries/Exp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exponential Power Series

This file defines the exponential power series `exp A = ∑ Xⁿ/n!` over ℚ-algebras and develops
its key properties, including the fundamental differential equation `(exp A)' = exp A`,
a uniqueness characterization, and the functional equation for multiplication.

## Main definitions

* `PowerSeries.exp`: The exponential power series `exp A = ∑ Xⁿ/n!` over a ℚ-algebra `A`.

## Main results

* `PowerSeries.coeff_exp`: The coefficient of `exp A` at `n` is `1/n!`.
* `PowerSeries.constantCoeff_exp`: The constant term of `exp A` is `1`.
* `PowerSeries.map_exp`: `exp` is preserved by ring homomorphisms between ℚ-algebras.
* `PowerSeries.derivative_exp`: The derivative of exp equals exp: `d⁄dX A (exp A) = exp A`.
* `PowerSeries.exp_unique_of_derivative_eq_self`: A power series with derivative equal to itself
  and constant term `1` must be `exp`.
* `PowerSeries.isUnit_exp`: `exp A` is a unit (invertible).
* `PowerSeries.order_exp`: The order of `exp A` is `0`.
* `PowerSeries.exp_mul_exp_eq_exp_add`: The functional equation `e^{aX} * e^{bX} = e^{(a+b)X}`.
* `PowerSeries.exp_mul_exp_neg_eq_one`: The identity `e^X * e^{-X} = 1`.
* `PowerSeries.exp_pow_eq_rescale_exp`: Powers of exp satisfy `(e^X)^k = e^{kX}`.
* `PowerSeries.exp_pow_sum`: Formula for the sum of powers of `exp`.
-/

namespace PowerSeries

variable (A A' : Type*) [Ring A] [Ring A'] [Algebra ℚ A] [Algebra ℚ A']

open Nat

def exp : PowerSeries A :=
  mk fun n => algebraMap ℚ A (1 / n !)

variable {A A'} (n : ℕ) (f : A →+* A')
