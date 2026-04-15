/-
Extracted from Data/Nat/Factors.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Prime numbers

This file deals with the factors of natural numbers.

## Important declarations

- `Nat.primeFactorsList n`: the prime factorization of `n`
- `Nat.primeFactorsList_unique`: uniqueness of the prime factorisation

-/

assert_not_exists Multiset

open Bool Subtype

open Nat

namespace Nat

def primeFactorsList : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | k + 2 =>
    let m := minFac (k + 2)
    m :: primeFactorsList ((k + 2) / m)

decreasing_by exact factors_lemma
