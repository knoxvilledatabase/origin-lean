/-
Extracted from Data/Nat/Factorization/Basic.lean
Genuine: 4 of 11 | Dissolved: 5 | Infrastructure: 2
-/
import Origin.Core

/-!
# Basic lemmas on prime factorizations
-/

open Finset List Finsupp

namespace Nat

variable {a b m n p : ℕ}

/-! ### Basic facts about factorization -/

/-! ## Lemmas characterising when `n.factorization p = 0` -/

theorem factorization_eq_zero_of_lt {n p : ℕ} (h : n < p) : n.factorization p = 0 :=
  Finsupp.notMem_support_iff.mp (mt le_of_mem_primeFactors (not_le_of_gt h))

-- DISSOLVED: dvd_of_factorization_pos

-- DISSOLVED: factorization_eq_zero_iff_remainder

theorem factorization_eq_zero_iff' (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 := by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp [Multiset.coe_eq_zero]

/-! ## Lemmas about factorizations of products and powers -/

-- DISSOLVED: factorization_prod_apply

/-! ## Lemmas about factorizations of primes and prime powers -/

theorem Prime.factorization_self {p : ℕ} (hp : Prime p) : p.factorization p = 1 := by simp [hp]

theorem factorization_pow_self {p n : ℕ} (hp : p.Prime) : (p ^ n).factorization p = n := by
  simp [factorization_pow, Prime.factorization_self hp]

-- DISSOLVED: eq_pow_of_factorization_eq_single

-- DISSOLVED: Prime.eq_of_factorization_pos

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/
