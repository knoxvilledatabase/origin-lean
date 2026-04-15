/-
Extracted from Data/Nat/Factorization/Defs.lean
Genuine: 20 of 31 | Dissolved: 9 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Padics.PadicVal.Defs

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
`RingTheory/UniqueFactorizationDomain`.

* Extend the inductions to any `NormalizationMonoid` with unique factorization.

-/

open Nat Finset List Finsupp

namespace Nat

variable {a b m n p : ℕ}

def factorization (n : ℕ) : ℕ →₀ ℕ where
  support := n.primeFactors
  toFun p := if p.Prime then padicValNat p n else 0
  mem_support_toFun := by simp [not_or]; aesop

@[simp] lemma support_factorization (n : ℕ) : (factorization n).support = n.primeFactors := rfl

theorem factorization_def (n : ℕ) {p : ℕ} (pp : p.Prime) : n.factorization p = padicValNat p n := by
  simpa [factorization] using absurd pp

@[simp]
theorem primeFactorsList_count_eq {n p : ℕ} : n.primeFactorsList.count p = n.factorization p := by
  rcases n.eq_zero_or_pos with (rfl | hn0)
  · simp [factorization, count]
  if pp : p.Prime then ?_ else
    rw [count_eq_zero_of_not_mem (mt prime_of_mem_primeFactorsList pp)]
    simp [factorization, pp]
  simp only [factorization_def _ pp]
  apply _root_.le_antisymm
  · rw [le_padicValNat_iff_replicate_subperm_primeFactorsList pp hn0.ne']
    exact List.le_count_iff_replicate_sublist.mp le_rfl |>.subperm
  · rw [← Nat.lt_add_one_iff, lt_iff_not_ge, ge_iff_le,
      le_padicValNat_iff_replicate_subperm_primeFactorsList pp hn0.ne']
    intro h
    have := h.count_le p
    simp at this

theorem factorization_eq_primeFactorsList_multiset (n : ℕ) :
    n.factorization = Multiset.toFinsupp (n.primeFactorsList : Multiset ℕ) := by
  ext p
  simp

alias factorization_eq_factors_multiset := factorization_eq_primeFactorsList_multiset

-- DISSOLVED: Prime.factorization_pos_of_dvd

-- DISSOLVED: multiplicity_eq_factorization

/-! ### Basic facts about factorization -/

-- DISSOLVED: factorization_prod_pow_eq_self

-- DISSOLVED: eq_of_factorization_eq

-- DISSOLVED: factorization_inj

@[simp]
theorem factorization_zero : factorization 0 = 0 := by ext; simp [factorization]

@[simp]
theorem factorization_one : factorization 1 = 0 := by ext; simp [factorization]

/-! ## Lemmas characterising when `n.factorization p = 0` -/

theorem factorization_eq_zero_iff (n p : ℕ) :
    n.factorization p = 0 ↔ ¬p.Prime ∨ ¬p ∣ n ∨ n = 0 := by
  simp_rw [← not_mem_support_iff, support_factorization, mem_primeFactors, not_and_or, not_ne_iff]

@[simp]
theorem factorization_eq_zero_of_non_prime (n : ℕ) {p : ℕ} (hp : ¬p.Prime) :
    n.factorization p = 0 := by simp [factorization_eq_zero_iff, hp]

@[simp]
theorem factorization_zero_right (n : ℕ) : n.factorization 0 = 0 :=
  factorization_eq_zero_of_non_prime _ not_prime_zero

theorem factorization_eq_zero_of_not_dvd {n p : ℕ} (h : ¬p ∣ n) : n.factorization p = 0 := by
  simp [factorization_eq_zero_iff, h]

theorem factorization_eq_zero_of_remainder {p r : ℕ} (i : ℕ) (hr : ¬p ∣ r) :
    (p * i + r).factorization p = 0 := by
  apply factorization_eq_zero_of_not_dvd
  rwa [← Nat.dvd_add_iff_right (Dvd.intro i rfl)]

/-! ## Lemmas about factorizations of products and powers -/

-- DISSOLVED: factorization_mul

-- DISSOLVED: factorization_le_iff_dvd

-- DISSOLVED: factorization_prod

@[simp]
theorem factorization_pow (n k : ℕ) : factorization (n ^ k) = k • n.factorization := by
  induction' k with k ih; · simp
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rw [Nat.pow_succ, mul_comm, factorization_mul hn (pow_ne_zero _ hn), ih,
    add_smul, one_smul, add_comm]

/-! ## Lemmas about factorizations of primes and prime powers -/

@[simp]
protected theorem Prime.factorization {p : ℕ} (hp : Prime p) : p.factorization = single p 1 := by
  ext q
  rw [← primeFactorsList_count_eq, primeFactorsList_prime hp, single_apply, count_singleton',
    if_congr eq_comm] <;> rfl

theorem Prime.factorization_pow {p k : ℕ} (hp : Prime p) : (p ^ k).factorization = single p k := by
  simp [hp]

-- DISSOLVED: pow_succ_factorization_not_dvd

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/

theorem prod_pow_factorization_eq_self {f : ℕ →₀ ℕ} (hf : ∀ p : ℕ, p ∈ f.support → Prime p) :
    (f.prod (· ^ ·)).factorization = f := by
  have h : ∀ x : ℕ, x ∈ f.support → x ^ f x ≠ 0 := fun p hp =>
    pow_ne_zero _ (Prime.ne_zero (hf p hp))
  simp only [Finsupp.prod, factorization_prod h]
  conv =>
    rhs
    rw [(sum_single f).symm]
  exact sum_congr rfl fun p hp => Prime.factorization_pow (hf p hp)

def factorizationEquiv : ℕ+ ≃ { f : ℕ →₀ ℕ | ∀ p ∈ f.support, Prime p } where
  toFun := fun ⟨n, _⟩ => ⟨n.factorization, fun _ => prime_of_mem_primeFactors⟩
  invFun := fun ⟨f, hf⟩ =>
    ⟨f.prod _, prod_pow_pos_of_zero_not_mem_support fun H => not_prime_zero (hf 0 H)⟩
  left_inv := fun ⟨_, hx⟩ => Subtype.ext <| factorization_prod_pow_eq_self hx.ne.symm
  right_inv := fun ⟨_, hf⟩ => Subtype.ext <| prod_pow_factorization_eq_self hf

/-! ### Factorization and coprimes -/

theorem factorization_mul_apply_of_coprime {p a b : ℕ} (hab : Coprime a b) :
    (a * b).factorization p = a.factorization p + b.factorization p := by
  simp only [← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul_of_coprime hab), count_append]

theorem factorization_mul_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext q
  rw [Finsupp.add_apply, factorization_mul_apply_of_coprime hab]

/-! ### Generalisation of the "even part" and "odd part" of a natural number -/

notation "ordProj[" p "] " n:arg => p ^ Nat.factorization n p

notation "ordCompl[" p "] " n:arg => n / ordProj[p] n

@[inherit_doc «termOrdProj[_]_»]
theorem ordProj_dvd (n p : ℕ) : ordProj[p] n ∣ n := by
  if hp : p.Prime then ?_ else simp [hp]
  rw [← primeFactorsList_count_eq]
  apply dvd_of_primeFactorsList_subperm (pow_ne_zero _ hp.ne_zero)
  rw [hp.primeFactorsList_pow, List.subperm_ext_iff]
  intro q hq
  simp [List.eq_of_mem_replicate hq]

/-! ### Factorization LCM definitions -/

def factorizationLCMLeft (a b : ℕ) : ℕ :=
  (Nat.lcm a b).factorization.prod fun p n ↦
    if b.factorization p ≤ a.factorization p then p ^ n else 1

def factorizationLCMRight (a b : ℕ) :=
  (Nat.lcm a b).factorization.prod fun p n ↦
    if b.factorization p ≤ a.factorization p then 1 else p ^ n

end Nat
