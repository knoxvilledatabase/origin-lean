/-
Extracted from RingTheory/UniqueFactorizationDomain/Nat.lean
Genuine: 1 of 4 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!
# Unique factorization of natural numbers

## Main definitions

* `Nat.instUniqueFactorizationMonoid`: the natural numbers have unique factorization
-/

assert_not_exists Field

namespace Nat

-- INSTANCE (free from Core): instWfDvdMonoid

-- INSTANCE (free from Core): instUniqueFactorizationMonoid

open UniqueFactorizationMonoid

-- DISSOLVED: factors_eq

lemma factors_multiset_prod_of_irreducible {s : Multiset ℕ} (h : ∀ x : ℕ, x ∈ s → Irreducible x) :
    normalizedFactors s.prod = s := by
  rw [← Multiset.rel_eq, ← associated_eq_eq]
  apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor h
    (prod_normalizedFactors _)
  rw [Ne, Multiset.prod_eq_zero_iff]
  exact fun con ↦ not_irreducible_zero (h 0 con)

end Nat
