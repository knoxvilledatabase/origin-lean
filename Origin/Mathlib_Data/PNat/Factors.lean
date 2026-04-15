/-
Extracted from Data/PNat/Factors.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Prime factors of nonzero naturals

This file defines the factorization of a nonzero natural number `n` as a multiset of primes,
the multiplicity of `p` in this factors multiset being the p-adic valuation of `n`.

## Main declarations

* `PrimeMultiset`: Type of multisets of prime numbers.
* `FactorMultiset n`: Multiset of prime factors of `n`.
-/

def PrimeMultiset :=
  Multiset Nat.Primes

deriving Inhabited, AddCommMonoid, DistribLattice,

  SemilatticeSup, Sub,

  IsOrderedCancelAddMonoid, CanonicallyOrderedAdd, OrderBot, OrderedSub

namespace PrimeMultiset

-- INSTANCE (free from Core): :

def ofPrime (p : Nat.Primes) : PrimeMultiset :=
  ({p} : Multiset Nat.Primes)
