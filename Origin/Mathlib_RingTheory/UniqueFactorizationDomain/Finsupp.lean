/-
Extracted from RingTheory/UniqueFactorizationDomain/Finsupp.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Factors as finsupp

## Main definitions
* `UniqueFactorizationMonoid.factorization`: the multiset of irreducible factors as a `Finsupp`.
-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

section Finsupp

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

variable [NormalizationMonoid α] [DecidableEq α]

open UniqueFactorizationMonoid

noncomputable def factorization (n : α) : α →₀ ℕ :=
  Multiset.toFinsupp (normalizedFactors n)

theorem factorization_eq_count {n p : α} :
    factorization n p = Multiset.count p (normalizedFactors n) := by simp [factorization]
