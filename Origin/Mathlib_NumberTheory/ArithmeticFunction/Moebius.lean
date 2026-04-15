/-
Extracted from NumberTheory/ArithmeticFunction/Moebius.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Möbius function and Möbius inversion

## Main Definitions

* `μ` is the Möbius function (spelled `moebius` in code; the notation `μ` is available by opening
  the namespace `ArithmeticFunction.Moebius`).

## Main Results

* Several forms of Möbius inversion:
* `sum_eq_iff_sum_mul_moebius_eq` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` for functions to a `CommGroupWithZero`
* And variants that apply when the equalities only hold on a set `S : Set ℕ` such that
  `m ∣ n → n ∈ S → m ∈ S`:
* `sum_eq_iff_sum_mul_moebius_eq_on` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq_on` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero` for functions to a `CommGroupWithZero`

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

open scoped zeta

def moebius : ArithmeticFunction ℤ :=
  ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩
