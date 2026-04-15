/-
Extracted from NumberTheory/ArithmeticFunction/Misc.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Miscellaneous arithmetic Functions

This file defines some simple examples of arithmetic functions (functions `ℕ → R` vanishing at
`0`, considered as a ring under Dirichlet convolution). Note that the Von Mangoldt and Möbius
functions are in separate files.

## Main Definitions

* `σ k` is the arithmetic function such that `σ k x = ∑ y ∈ divisors x, y ^ k` for `0 < x`.
* `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
* `id` is the identity arithmetic function on `ℕ`.
* `ω n` is the number of distinct prime factors of `n`.
* `Ω n` is the number of prime factors of `n` counted with multiplicity.

## Notation

The arithmetic functions `σ`, `ω` and `Ω` have Greek letter names.
This notation is scoped to the separate locales `ArithmeticFunction.sigma` for `σ`,
`ArithmeticFunction.omega` for `ω` and `ArithmeticFunction.Omega` for `Ω`, to allow for selective
access.

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

section SpecialFunctions

open scoped zeta

section ProdPrimeFactors

def prodPrimeFactors [CommMonoidWithZero R] (f : ℕ → R) : ArithmeticFunction R where
  toFun d := if d = 0 then 0 else ∏ p ∈ d.primeFactors, f p
  map_zero' := if_pos rfl

open Batteries.ExtendedBinder

scoped syntax (name := bigproddvd) "∏ᵖ " extBinder " ∣ " term ", " term:67 : term

scoped macro_rules (kind := bigproddvd)

  | `(∏ᵖ $x:ident ∣ $n, $r) => `(prodPrimeFactors (fun $x ↦ $r) $n)
