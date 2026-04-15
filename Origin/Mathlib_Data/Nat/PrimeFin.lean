/-
Extracted from Data/Nat/PrimeFin.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Prime numbers

This file contains some results about prime numbers which depend on finiteness of sets.
-/

open Finset

namespace Nat

variable {a b k m n p : ℕ}

theorem infinite_setOf_prime : { p | Prime p }.Infinite :=
  Set.infinite_of_not_bddAbove not_bddAbove_setOf_prime

-- INSTANCE (free from Core): Primes.infinite

-- INSTANCE (free from Core): Primes.countable

def primeFactors (n : ℕ) : Finset ℕ := n.primeFactorsList.toFinset
