/-
Extracted from Data/Nat/Digits/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Digits of a natural number

This provides a basic API for extracting the digits of a natural number in a given base,
and reconstructing numbers from their digits.

We also prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

Also included is a bound on the length of `Nat.toDigits` from core.

## TODO

A basic `norm_digits` tactic for proving goals of the form `Nat.digits a b = l` where `a` and `b`
are numerals is not yet ported.
-/

assert_not_exists Finset

namespace Nat

variable {n : ℕ}

def digitsAux0 : ℕ → List ℕ
  | 0 => []
  | n + 1 => [n+1]

def digitsAux1 (n : ℕ) : List ℕ :=
  List.replicate n 1
