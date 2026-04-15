/-
Extracted from Data/Nat/Factorization/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Prime factorizations

`n.factorization` is the finitely supported function `ℕ →₀ ℕ`
mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
* `factorization 2000 2` is 4
* `factorization 2000 5` is 3
* `factorization 2000 k` is 0 for all other `k : ℕ`.

## TODO

* As discussed in this Zulip thread:
  https://leanprover.zulipchat.com/#narrow/stream/217875/topic/Multiplicity.20in.20the.20naturals
  We have lots of disparate ways of talking about the multiplicity of a prime
  in a natural number, including `factors.count`, `padicValNat`, `multiplicity`,
  and the material in `Data/PNat/Factors`.  Move some of this material to this file,
  prove results about the relationships between these definitions,
  and (where appropriate) choose a uniform canonical way of expressing these ideas.

* Moreover, the results here should be generalised to an arbitrary unique factorization monoid
  with a normalization function, and then deduplicated.  The basics of this have been started in
  `Mathlib/RingTheory/UniqueFactorizationDomain/`.

* Extend the inductions to any `NormalizationMonoid` with unique factorization.

-/

open Nat Finset List Finsupp

namespace Nat

variable {a b m n p : ℕ}

def factorization (n : ℕ) : ℕ →₀ ℕ where
  support := n.primeFactors
  toFun p := if p.Prime then padicValNat p n else 0
  mem_support_toFun := by simp [not_or]; aesop
