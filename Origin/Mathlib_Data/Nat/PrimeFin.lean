/-
Extracted from Data/Nat/PrimeFin.lean
Genuine: 15 of 26 | Dissolved: 8 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Set.Finite.Lattice

/-!
# Prime numbers

This file contains some results about prime numbers which depend on finiteness of sets.
-/

open Finset

namespace Nat

variable {a b k m n p : ℕ}

theorem infinite_setOf_prime : { p | Prime p }.Infinite :=
  Set.infinite_of_not_bddAbove not_bddAbove_setOf_prime

instance Primes.infinite : Infinite Primes := infinite_setOf_prime.to_subtype

instance Primes.countable : Countable Primes := ⟨⟨coeNat.coe, coe_nat_injective⟩⟩

def primeFactors (n : ℕ) : Finset ℕ := n.primeFactorsList.toFinset

@[simp] lemma toFinset_factors (n : ℕ) : n.primeFactorsList.toFinset = n.primeFactors := rfl

-- DISSOLVED: mem_primeFactors

-- DISSOLVED: mem_primeFactors_of_ne_zero

-- DISSOLVED: primeFactors_mono

lemma mem_primeFactors_iff_mem_primeFactorsList : p ∈ n.primeFactors ↔ p ∈ n.primeFactorsList := by
  simp only [primeFactors, List.mem_toFinset]

alias mem_primeFactors_iff_mem_factors := mem_primeFactors_iff_mem_primeFactorsList

lemma prime_of_mem_primeFactors (hp : p ∈ n.primeFactors) : p.Prime := (mem_primeFactors.1 hp).1

lemma dvd_of_mem_primeFactors (hp : p ∈ n.primeFactors) : p ∣ n := (mem_primeFactors.1 hp).2.1

lemma pos_of_mem_primeFactors (hp : p ∈ n.primeFactors) : 0 < p :=
  (prime_of_mem_primeFactors hp).pos

lemma le_of_mem_primeFactors (h : p ∈ n.primeFactors) : p ≤ n :=
  le_of_dvd (mem_primeFactors.1 h).2.2.bot_lt <| dvd_of_mem_primeFactors h

@[simp] lemma primeFactors_zero : primeFactors 0 = ∅ := by
  ext
  simp

@[simp] lemma primeFactors_one : primeFactors 1 = ∅ := by
  ext
  simpa using Prime.ne_one

@[simp] lemma primeFactors_eq_empty : n.primeFactors = ∅ ↔ n = 0 ∨ n = 1 := by
  constructor
  · contrapose!
    rintro hn
    obtain ⟨p, hp, hpn⟩ := exists_prime_and_dvd hn.2
    exact Nonempty.ne_empty <| ⟨_, mem_primeFactors.2 ⟨hp, hpn, hn.1⟩⟩
  · rintro (rfl | rfl) <;> simp

@[simp]
lemma nonempty_primeFactors {n : ℕ} : n.primeFactors.Nonempty ↔ 1 < n := by
  rw [← not_iff_not, Finset.not_nonempty_iff_eq_empty, primeFactors_eq_empty, not_lt,
    Nat.le_one_iff_eq_zero_or_eq_one]

@[simp] protected lemma Prime.primeFactors (hp : p.Prime) : p.primeFactors = {p} := by
  simp [Nat.primeFactors, primeFactorsList_prime hp]

-- DISSOLVED: primeFactors_mul

lemma Coprime.primeFactors_mul {a b : ℕ} (hab : Coprime a b) :
    (a * b).primeFactors = a.primeFactors ∪ b.primeFactors :=
  (List.toFinset.ext <| mem_primeFactorsList_mul_of_coprime hab).trans <| List.toFinset_union _ _

-- DISSOLVED: primeFactors_gcd

-- DISSOLVED: disjoint_primeFactors

protected lemma Coprime.disjoint_primeFactors (hab : Coprime a b) :
    Disjoint a.primeFactors b.primeFactors :=
  List.disjoint_toFinset_iff_disjoint.2 <| coprime_primeFactorsList_disjoint hab

lemma primeFactors_pow_succ (n k : ℕ) : (n ^ (k + 1)).primeFactors = n.primeFactors := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  induction' k with k ih
  · simp
  · rw [pow_succ', primeFactors_mul hn (pow_ne_zero _ hn), ih, Finset.union_idempotent]

-- DISSOLVED: primeFactors_pow

-- DISSOLVED: primeFactors_prime_pow

end Nat
