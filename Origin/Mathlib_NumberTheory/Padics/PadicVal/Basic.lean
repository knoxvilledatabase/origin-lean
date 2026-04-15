/-
Extracted from NumberTheory/Padics/PadicVal/Basic.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in
`Mathlib/NumberTheory/Padics/PadicNorm.lean`.

## Notation

This file uses the local notation `/.` for `Rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## Calculations with `p`-adic valuations

* `padicValNat_factorial`: Legendre's Theorem. The `p`-adic valuation of `n!` is the sum of the
  quotients `n / p ^ i`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound
  greater than `log p n`. See `Nat.Prime.multiplicity_factorial` for the same result but stated in
  the language of prime multiplicity.

* `sub_one_mul_padicValNat_factorial`: Legendre's Theorem.  Taking (`p - 1`) times
  the `p`-adic valuation of `n!` equals `n` minus the sum of base `p` digits of `n`.

* `padicValNat_choose`: Kummer's Theorem. The `p`-adic valuation of `n.choose k` is the number
  of carries when `k` and `n - k` are added in base `p`. This sum is expressed over the finset
  `Ico 1 b` where `b` is any bound greater than `log p n`. See `Nat.Prime.multiplicity_choose` for
  the same result but stated in the language of prime multiplicity.

* `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`: Kummer's Theorem. Taking (`p - 1`) times the
  `p`-adic valuation of the binomial `n` over `k` equals the sum of the digits of `k` plus the sum
  of the digits of `n - k` minus the sum of digits of `n`, all base `p`.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

universe u

open Nat Rat

open scoped Finset

namespace padicValNat

variable {p : ℕ}

alias self := padicValNat_base

theorem eq_zero_of_not_dvd {n : ℕ} (h : ¬p ∣ n) : padicValNat p n = 0 :=
  eq_zero_iff.2 <| Or.inr <| Or.inr h

end padicValNat

def padicValInt (p : ℕ) (z : ℤ) : ℕ :=
  padicValNat p z.natAbs

namespace padicValInt

variable {p : ℕ}

-- DISSOLVED: of_ne_one_ne_zero
