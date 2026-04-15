/-
Extracted from NumberTheory/Primorial.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Primorial

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n`.

## Notation

We use the local notation `n#` for the primorial of `n`: that is, the product of the primes less
than or equal to `n`.
-/

open Finset

open Nat

def primorial (n : ℕ) : ℕ := ∏ p ∈ range (n + 1) with p.Prime, p

local notation x "#" => primorial x
