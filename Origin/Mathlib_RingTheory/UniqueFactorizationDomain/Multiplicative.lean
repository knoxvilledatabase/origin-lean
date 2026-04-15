/-
Extracted from RingTheory/UniqueFactorizationDomain/Multiplicative.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Multiplicative maps on unique factorization domains

## Main results
* `UniqueFactorizationMonoid.induction_on_coprime`: if `P` holds for `0`, units and powers of
  primes, and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`, then `P` holds on all `a : α`.
* `UniqueFactorizationMonoid.multiplicative_of_coprime`: if `f` maps `p ^ i` to `(f p) ^ i` for
  primes `p`, and `f` is multiplicative on coprime elements, then `f` is multiplicative everywhere.
-/

assert_not_exists Field

variable {α : Type*}

namespace UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

section Multiplicative

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

variable {β : Type*} [CommMonoidWithZero β]

theorem prime_pow_coprime_prod_of_coprime_insert [DecidableEq α] {s : Finset α} (i : α → ℕ) (p : α)
    (hps : p ∉ s) (is_prime : ∀ q ∈ insert p s, Prime q)
    (is_coprime : ∀ᵉ (q ∈ insert p s) (q' ∈ insert p s), q ∣ q' → q = q') :
    IsRelPrime (p ^ i p) (∏ p' ∈ s, p' ^ i p') := by
  have hp := is_prime _ (Finset.mem_insert_self _ _)
  refine (isRelPrime_iff_no_prime_factors <| pow_ne_zero _ hp.ne_zero).mpr ?_
  intro d hdp hdprod hd
  apply hps
  replace hdp := hd.dvd_of_dvd_pow hdp
  obtain ⟨q, q_mem', hdq⟩ := hd.exists_mem_multiset_dvd hdprod
  obtain ⟨q, q_mem, rfl⟩ := Multiset.mem_map.mp q_mem'
  replace hdq := hd.dvd_of_dvd_pow hdq
  have : p ∣ q := dvd_trans (hd.irreducible.dvd_symm hp.irreducible hdp) hdq
  convert q_mem using 0
  rw [Finset.mem_val,
    is_coprime _ (Finset.mem_insert_self p s) _ (Finset.mem_insert_of_mem q_mem) this]
