/-
Extracted from NumberTheory/Divisors.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Divisor Finsets

This file defines sets of divisors of a natural number. This is particularly useful as background
for defining Dirichlet convolution.

## Main Definitions
Let `n : ℕ`. All of the following definitions are in the `Nat` namespace:
* `divisors n` is the `Finset` of natural numbers that divide `n`.
* `properDivisors n` is the `Finset` of natural numbers that divide `n`, other than `n`.
* `divisorsAntidiagonal n` is the `Finset` of pairs `(x,y)` such that `x * y = n`.
* `Perfect n` is true when `n` is positive and the sum of `properDivisors n` is `n`.

## Conventions

Since `0` has infinitely many divisors, none of the definitions in this file make sense for it.
Therefore we adopt the convention that `Nat.divisors 0`, `Nat.properDivisors 0`,
`Nat.divisorsAntidiagonal 0` and `Int.divisorsAntidiag 0` are all `∅`.

## Tags
divisors, perfect numbers

-/

open Finset

namespace Nat

variable (n : ℕ)

def divisors : Finset ℕ := {d ∈ Ico 1 (n + 1) | d ∣ n}

def properDivisors : Finset ℕ := {d ∈ Ico 1 n | d ∣ n}

def divisorsAntidiagonal : Finset (ℕ × ℕ) :=
  (Icc 1 n).filterMap (fun x ↦ let y := n / x; if x * y = n then some (x, y) else none)
    fun x₁ x₂ (x, y) hx₁ hx₂ ↦ by aesop

def divisorsAntidiagonalList (n : ℕ) : List (ℕ × ℕ) :=
  (List.range' 1 n).filterMap
    (fun x ↦ let y := n / x; if x * y = n then some (x, y) else none)

variable {n}
