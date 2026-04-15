/-
Extracted from Data/Nat/Factors.lean
Genuine: 22 of 38 | Dissolved: 16 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Prime
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Subperm

/-!
# Prime numbers

This file deals with the factors of natural numbers.

## Important declarations

- `Nat.factors n`: the prime factorization of `n`
- `Nat.factors_unique`: uniqueness of the prime factorisation

-/

open Bool Subtype

open Nat

namespace Nat

def primeFactorsList : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | k + 2 =>
    let m := minFac (k + 2)
    m :: primeFactorsList ((k + 2) / m)

decreasing_by show (k + 2) / m < (k + 2); exact factors_lemma

@[simp]
theorem primeFactorsList_zero : primeFactorsList 0 = [] := by rw [primeFactorsList]

@[simp]
theorem primeFactorsList_one : primeFactorsList 1 = [] := by rw [primeFactorsList]

@[simp]
theorem primeFactorsList_two : primeFactorsList 2 = [2] := by simp [primeFactorsList]

theorem prime_of_mem_primeFactorsList {n : ℕ} : ∀ {p : ℕ}, p ∈ primeFactorsList n → Prime p := by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro p h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      have h₁ : p = m ∨ p ∈ primeFactorsList ((k + 2) / m) :=
        List.mem_cons.1 (by rwa [primeFactorsList] at h)
      exact Or.casesOn h₁ (fun h₂ => h₂.symm ▸ minFac_prime (by simp)) prime_of_mem_primeFactorsList

theorem pos_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ primeFactorsList n) : 0 < p :=
  Prime.pos (prime_of_mem_primeFactorsList h)

-- DISSOLVED: prod_primeFactorsList

theorem primeFactorsList_prime {p : ℕ} (hp : Nat.Prime p) : p.primeFactorsList = [p] := by
  have : p = p - 2 + 2 := Nat.eq_add_of_sub_eq hp.two_le rfl
  rw [this, primeFactorsList]
  simp only [Eq.symm this]
  have : Nat.minFac p = p := (Nat.prime_def_minFac.mp hp).2
  simp only [this, primeFactorsList, Nat.div_self (Nat.Prime.pos hp)]

theorem primeFactorsList_chain {n : ℕ} :
    ∀ {a}, (∀ p, Prime p → p ∣ n → a ≤ p) → List.Chain (· ≤ ·) a (primeFactorsList n) := by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro a h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      rw [primeFactorsList]
      refine List.Chain.cons ((le_minFac.2 h).resolve_left (by simp)) (primeFactorsList_chain ?_)
      exact fun p pp d => minFac_le_of_dvd pp.two_le (d.trans <| div_dvd_of_dvd <| minFac_dvd _)

theorem primeFactorsList_chain_2 (n) : List.Chain (· ≤ ·) 2 (primeFactorsList n) :=
  primeFactorsList_chain fun _ pp _ => pp.two_le

theorem primeFactorsList_chain' (n) : List.Chain' (· ≤ ·) (primeFactorsList n) :=
  @List.Chain'.tail _ _ (_ :: _) (primeFactorsList_chain_2 _)

theorem primeFactorsList_sorted (n : ℕ) : List.Sorted (· ≤ ·) (primeFactorsList n) :=
  List.chain'_iff_pairwise.1 (primeFactorsList_chain' _)

theorem primeFactorsList_add_two (n : ℕ) :
    primeFactorsList (n + 2) = minFac (n + 2) :: primeFactorsList ((n + 2) / minFac (n + 2)) := by
  rw [primeFactorsList]

@[simp]
theorem primeFactorsList_eq_nil (n : ℕ) : n.primeFactorsList = [] ↔ n = 0 ∨ n = 1 := by
  constructor <;> intro h
  · rcases n with (_ | _ | n)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [primeFactorsList] at h
      injection h
  · rcases h with (rfl | rfl)
    · exact primeFactorsList_zero
    · exact primeFactorsList_one

open scoped List in

-- DISSOLVED: eq_of_perm_primeFactorsList

section

open List

-- DISSOLVED: mem_primeFactorsList_iff_dvd

theorem dvd_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ n.primeFactorsList) : p ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact dvd_zero p
  · rwa [← mem_primeFactorsList_iff_dvd hn.ne' (prime_of_mem_primeFactorsList h)]

-- DISSOLVED: mem_primeFactorsList

-- DISSOLVED: mem_primeFactorsList'

theorem le_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ n.primeFactorsList) : p ≤ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · rw [primeFactorsList_zero] at h
    cases h
  · exact le_of_dvd hn (dvd_of_mem_primeFactorsList h)

theorem primeFactorsList_unique {n : ℕ} {l : List ℕ} (h₁ : prod l = n) (h₂ : ∀ p ∈ l, Prime p) :
    l ~ primeFactorsList n := by
  refine perm_of_prod_eq_prod ?_ ?_ ?_
  · rw [h₁]
    refine (prod_primeFactorsList ?_).symm
    rintro rfl
    rw [prod_eq_zero_iff] at h₁
    exact Prime.ne_zero (h₂ 0 h₁) rfl
  · simp_rw [← prime_iff]
    exact h₂
  · simp_rw [← prime_iff]
    exact fun p => prime_of_mem_primeFactorsList

theorem Prime.primeFactorsList_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (p ^ n).primeFactorsList = List.replicate n p := by
  symm
  rw [← List.replicate_perm]
  apply Nat.primeFactorsList_unique (List.prod_replicate n p)
  intro q hq
  rwa [eq_of_mem_replicate hq]

-- DISSOLVED: eq_prime_pow_of_unique_prime_dvd

-- DISSOLVED: perm_primeFactorsList_mul

theorem perm_primeFactorsList_mul_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  exact perm_primeFactorsList_mul ha.ne' hb.ne'

-- DISSOLVED: primeFactorsList_sublist_right

-- DISSOLVED: primeFactorsList_sublist_of_dvd

-- DISSOLVED: primeFactorsList_subset_right

-- DISSOLVED: primeFactorsList_subset_of_dvd

-- DISSOLVED: dvd_of_primeFactorsList_subperm

-- DISSOLVED: replicate_subperm_primeFactorsList_iff

end

-- DISSOLVED: mem_primeFactorsList_mul

theorem coprime_primeFactorsList_disjoint {a b : ℕ} (hab : a.Coprime b) :
    List.Disjoint a.primeFactorsList b.primeFactorsList := by
  intro q hqa hqb
  apply not_prime_one
  rw [← eq_one_of_dvd_coprimes hab (dvd_of_mem_primeFactorsList hqa)
    (dvd_of_mem_primeFactorsList hqb)]
  exact prime_of_mem_primeFactorsList hqa

theorem mem_primeFactorsList_mul_of_coprime {a b : ℕ} (hab : Coprime a b) (p : ℕ) :
    p ∈ (a * b).primeFactorsList ↔ p ∈ a.primeFactorsList ∪ b.primeFactorsList := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  rw [mem_primeFactorsList_mul ha.ne' hb.ne', List.mem_union_iff]

open List

-- DISSOLVED: mem_primeFactorsList_mul_left

-- DISSOLVED: mem_primeFactorsList_mul_right

theorem eq_two_pow_or_exists_odd_prime_and_dvd (n : ℕ) :
    (∃ k : ℕ, n = 2 ^ k) ∨ ∃ p, Nat.Prime p ∧ p ∣ n ∧ Odd p :=
  (eq_or_ne n 0).elim (fun hn => Or.inr ⟨3, prime_three, hn.symm ▸ dvd_zero 3, ⟨1, rfl⟩⟩) fun hn =>
    or_iff_not_imp_right.mpr fun H =>
      ⟨n.primeFactorsList.length,
        eq_prime_pow_of_unique_prime_dvd hn fun {_} hprime hdvd =>
          hprime.eq_two_or_odd'.resolve_right fun hodd => H ⟨_, hprime, hdvd, hodd⟩⟩

theorem four_dvd_or_exists_odd_prime_and_dvd_of_two_lt {n : ℕ} (n2 : 2 < n) :
    4 ∣ n ∨ ∃ p, Prime p ∧ p ∣ n ∧ Odd p := by
  obtain ⟨_ | _ | k, rfl⟩ | ⟨p, hp, hdvd, hodd⟩ := n.eq_two_pow_or_exists_odd_prime_and_dvd
  · contradiction
  · contradiction
  · simp [Nat.pow_succ, mul_assoc]
  · exact Or.inr ⟨p, hp, hdvd, hodd⟩

end Nat
