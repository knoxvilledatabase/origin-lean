/-
Extracted from RingTheory/Radical/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Radical of an element of a unique factorization normalization monoid

This file defines the radical of an element `a` in a unique factorization normalization
monoid as the product of normalized prime factors of `a` without duplication.
This is different from the radical of an ideal.

Lemmas relating to natural numbers and integers are in `Mathlib.RingTheory.Radical.NatInt`.

## Main declarations

- `radical`: The radical of an element `a` in a unique factorization monoid is the product of
  its prime factors.
- `radical_eq_of_associated`: If `a` and `b` are associates, i.e. `a * u = b` for some unit `u`,
  then `radical a = radical b`.
- `radical_mul_of_isUnit_left`: Multiplying by a unit does not change the radical.
- `radical_dvd_self`: `radical a` divides `a`.
- `radical_pow`: `radical (a ^ n) = radical a` for any `n ≥ 1`.
- `radical_of_prime`: Radical of a prime element is equal to its normalization.
- `radical_pow_of_prime`: Radical of a power of a prime element is equal to its normalization.
- `radical_mul`, `radical_prod`: Radical is multiplicative for (pairwise) relatively prime elements.
- `radical_mul_dvd`, `radical_prod_dvd`: Radical of a product divides the product of radicals.

### For Euclidean domains

- `EuclideanDomain.divRadical`: For an element `a` in a Euclidean domain, `a / radical a`.
- `EuclideanDomain.divRadical_mul`: `divRadical` of a product is the product of `divRadical`s.
- `IsCoprime.divRadical`: `divRadical` of coprime elements are coprime.

## TODO

- Connect this notion with `Ideal.radical`. Particularly, for a principal ideal,
  `Ideal.radical (Ideal.span {a}) = Ideal.span {radical a}`.
-/

namespace UniqueFactorizationMonoid

variable {M : Type*} [CommMonoidWithZero M] [NormalizationMonoid M]
  [UniqueFactorizationMonoid M] {a b u : M}

open scoped Classical in

def primeFactors (a : M) : Finset M :=
  (normalizedFactors a).toFinset

lemma mem_primeFactors : a ∈ primeFactors b ↔ a ∈ normalizedFactors b := by
  simp only [primeFactors, Multiset.mem_toFinset]

theorem _root_.Associated.primeFactors_eq {a b : M} (h : Associated a b) :
    primeFactors a = primeFactors b := by
  unfold primeFactors
  rw [h.normalizedFactors_eq]
