/-
Extracted from RingTheory/Radical/NatInt.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The radical in `ℕ` and `ℤ`

## Declarations for `ℕ`

- `UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors`: The prime factors of a natural number
  are the same as the prime factors defined in `Nat.primeFactors`.
- `Nat.radical_eq_prod_primeFactors`: The radical is computable for natural numbers.
- `Nat.radical_le_self_iff`: if `n ≠ 0`, `radical n ≤ n`.
- `Nat.two_le_radical_iff`: `2 ≤ n.radical` iff `2 ≤ n`.

## Declarations for `ℤ`

- `UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs`: The prime factors of an integer
  are the same as the prime factors of its absolute value.
- `Int.radical_eq_prod_primeFactors`: The radical is computable for integers.
-/

open UniqueFactorizationMonoid

/-! ### Lemmas about natural numbers -/

lemma UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors :
    primeFactors = Nat.primeFactors := by
  ext n : 1
  rw [primeFactors, Nat.factors_eq, Nat.primeFactors]
  -- this convert is necessary because of the different DecidableEq instances
  convert List.toFinset_coe _

namespace Nat

variable {n : ℕ}

lemma radical_eq_prod_primeFactors : radical n = ∏ p ∈ n.primeFactors, p := by
  simp [radical, primeFactors_eq_natPrimeFactors]

lemma radical_pos (n) : 0 < radical n := pos_of_ne_zero radical_ne_zero
