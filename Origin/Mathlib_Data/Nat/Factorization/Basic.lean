/-
Extracted from Data/Nat/Factorization/Basic.lean
Genuine: 35 | Conflates: 0 | Dissolved: 32 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases

/-!
# Basic lemmas on prime factorizations
-/

open Finset List Finsupp

namespace Nat

variable {a b m n p : ℕ}

/-! ### Basic facts about factorization -/

/-! ## Lemmas characterising when `n.factorization p = 0` -/

theorem factorization_eq_zero_of_lt {n p : ℕ} (h : n < p) : n.factorization p = 0 :=
  Finsupp.not_mem_support_iff.mp (mt le_of_mem_primeFactors (not_le_of_lt h))

@[simp]
theorem factorization_one_right (n : ℕ) : n.factorization 1 = 0 :=
  factorization_eq_zero_of_non_prime _ not_prime_one

-- DISSOLVED: dvd_of_factorization_pos

-- DISSOLVED: factorization_eq_zero_iff_remainder

theorem factorization_eq_zero_iff' (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 := by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp [factorization, AddEquiv.map_eq_zero_iff, Multiset.coe_eq_zero]

/-! ## Lemmas about factorizations of products and powers -/

lemma prod_factorization_eq_prod_primeFactors {β : Type*} [CommMonoid β] (f : ℕ → ℕ → β) :
    n.factorization.prod f = ∏ p ∈ n.primeFactors, f p (n.factorization p) := rfl

lemma prod_primeFactors_prod_factorization {β : Type*} [CommMonoid β] (f : ℕ → β) :
    ∏ p ∈ n.primeFactors, f p = n.factorization.prod (fun p _ ↦ f p) := rfl

/-! ## Lemmas about factorizations of primes and prime powers -/

@[simp]
theorem Prime.factorization_self {p : ℕ} (hp : Prime p) : p.factorization p = 1 := by simp [hp]

-- DISSOLVED: eq_pow_of_factorization_eq_single

-- DISSOLVED: Prime.eq_of_factorization_pos

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/

-- DISSOLVED: eq_factorization_iff

theorem factorizationEquiv_inv_apply {f : ℕ →₀ ℕ} (hf : ∀ p ∈ f.support, Prime p) :
    (factorizationEquiv.symm ⟨f, hf⟩).1 = f.prod (· ^ ·) :=
  rfl

@[simp]
theorem ordProj_of_not_prime (n p : ℕ) (hp : ¬p.Prime) : ordProj[p] n = 1 := by
  simp [factorization_eq_zero_of_non_prime n hp]

@[simp]
theorem ordCompl_of_not_prime (n p : ℕ) (hp : ¬p.Prime) : ordCompl[p] n = n := by
  simp [factorization_eq_zero_of_non_prime n hp]

theorem ordCompl_dvd (n p : ℕ) : ordCompl[p] n ∣ n :=
  div_dvd_of_dvd (ordProj_dvd n p)

theorem ordProj_pos (n p : ℕ) : 0 < ordProj[p] n := by
  if pp : p.Prime then simp [pow_pos pp.pos] else simp [pp]

-- DISSOLVED: ordProj_le

-- DISSOLVED: ordCompl_pos

theorem ordCompl_le (n p : ℕ) : ordCompl[p] n ≤ n :=
  Nat.div_le_self _ _

theorem ordProj_mul_ordCompl_eq_self (n p : ℕ) : ordProj[p] n * ordCompl[p] n = n :=
  Nat.mul_div_cancel' (ordProj_dvd n p)

alias ord_proj_mul_ord_compl_eq_self := ordProj_mul_ordCompl_eq_self

-- DISSOLVED: ordProj_mul

theorem ordCompl_mul (a b p : ℕ) : ordCompl[p] (a * b) = ordCompl[p] a * ordCompl[p] b := by
  if ha : a = 0 then simp [ha] else
  if hb : b = 0 then simp [hb] else
  simp only [ordProj_mul p ha hb]
  rw [div_mul_div_comm (ordProj_dvd a p) (ordProj_dvd b p)]

/-! ### Factorization and divisibility -/

-- DISSOLVED: factorization_lt

theorem factorization_le_of_le_pow {n p b : ℕ} (hb : n ≤ p ^ b) : n.factorization p ≤ b := by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then
    exact (Nat.pow_le_pow_iff_right pp.one_lt).1 ((ordProj_le p hn).trans hb)
  else
    simp [factorization_eq_zero_of_non_prime n pp]

-- DISSOLVED: factorization_prime_le_iff_dvd

-- DISSOLVED: factorization_le_factorization_mul_left

-- DISSOLVED: factorization_le_factorization_mul_right

-- DISSOLVED: Prime.pow_dvd_iff_le_factorization

-- DISSOLVED: Prime.pow_dvd_iff_dvd_ordProj

alias Prime.pow_dvd_iff_dvd_ord_proj := Prime.pow_dvd_iff_dvd_ordProj

-- DISSOLVED: Prime.dvd_iff_one_le_factorization

-- DISSOLVED: exists_factorization_lt_of_lt

@[simp]
theorem factorization_div {d n : ℕ} (h : d ∣ n) :
    (n / d).factorization = n.factorization - d.factorization := by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [zero_dvd_iff.mp h]
  rcases eq_or_ne n 0 with (rfl | hn); · simp [tsub_eq_zero_of_le]
  apply add_left_injective d.factorization
  simp only
  rw [tsub_add_cancel_of_le <| (Nat.factorization_le_iff_dvd hd hn).mpr h, ←
    Nat.factorization_mul (Nat.div_pos (Nat.le_of_dvd hn.bot_lt h) hd.bot_lt).ne' hd,
    Nat.div_mul_cancel h]

-- DISSOLVED: dvd_ordProj_of_dvd

-- DISSOLVED: not_dvd_ordCompl

-- DISSOLVED: coprime_ordCompl

theorem factorization_ordCompl (n p : ℕ) :
    (ordCompl[p] n).factorization = n.factorization.erase p := by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then ?_ else
    -- Porting note: needed to solve side goal explicitly
    rw [Finsupp.erase_of_not_mem_support] <;> simp [pp]
  ext q
  rcases eq_or_ne q p with (rfl | hqp)
  · simp only [Finsupp.erase_same, factorization_eq_zero_iff, not_dvd_ordCompl pp hn]
    simp
  · rw [Finsupp.erase_ne hqp, factorization_div (ordProj_dvd n p)]
    simp [pp.factorization, hqp.symm]

theorem dvd_ordCompl_of_dvd_not_dvd {p d n : ℕ} (hdn : d ∣ n) (hpd : ¬p ∣ d) :
    d ∣ ordCompl[p] n := by
  if hn0 : n = 0 then simp [hn0] else
  if hd0 : d = 0 then simp [hd0] at hpd else
  rw [← factorization_le_iff_dvd hd0 (ordCompl_pos p hn0).ne', factorization_ordCompl]
  intro q
  if hqp : q = p then
    simp [factorization_eq_zero_iff, hqp, hpd]
  else
    simp [hqp, (factorization_le_iff_dvd hd0 hn0).2 hdn q]

alias dvd_ord_compl_of_dvd_not_dvd := dvd_ordCompl_of_dvd_not_dvd

-- DISSOLVED: exists_eq_pow_mul_and_not_dvd

-- DISSOLVED: exists_eq_two_pow_mul_odd

-- DISSOLVED: dvd_iff_div_factorization_eq_tsub

-- DISSOLVED: ordProj_dvd_ordProj_of_dvd

alias ord_proj_dvd_ord_proj_of_dvd := ordProj_dvd_ordProj_of_dvd

-- DISSOLVED: ordProj_dvd_ordProj_iff_dvd

alias ord_proj_dvd_ord_proj_iff_dvd := ordProj_dvd_ordProj_iff_dvd

theorem ordCompl_dvd_ordCompl_of_dvd {a b : ℕ} (hab : a ∣ b) (p : ℕ) :
    ordCompl[p] a ∣ ordCompl[p] b := by
  rcases em' p.Prime with (pp | pp)
  · simp [pp, hab]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  rcases eq_or_ne a 0 with (rfl | ha0)
  · cases hb0 (zero_dvd_iff.1 hab)
  have ha := (Nat.div_pos (ordProj_le p ha0) (ordProj_pos a p)).ne'
  have hb := (Nat.div_pos (ordProj_le p hb0) (ordProj_pos b p)).ne'
  rw [← factorization_le_iff_dvd ha hb, factorization_ordCompl a p, factorization_ordCompl b p]
  intro q
  rcases eq_or_ne q p with (rfl | hqp)
  · simp
  simp_rw [erase_ne hqp]
  exact (factorization_le_iff_dvd ha0 hb0).2 hab q

alias ord_compl_dvd_ord_compl_of_dvd := ordCompl_dvd_ordCompl_of_dvd

theorem ordCompl_dvd_ordCompl_iff_dvd (a b : ℕ) :
    (∀ p : ℕ, ordCompl[p] a ∣ ordCompl[p] b) ↔ a ∣ b := by
  refine ⟨fun h => ?_, fun hab p => ordCompl_dvd_ordCompl_of_dvd hab p⟩
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  if pa : a.Prime then ?_ else simpa [pa] using h a
  if pb : b.Prime then ?_ else simpa [pb] using h b
  rw [prime_dvd_prime_iff_eq pa pb]
  by_contra hab
  apply pa.ne_one
  rw [← Nat.dvd_one, ← Nat.mul_dvd_mul_iff_left hb0.bot_lt, mul_one]
  simpa [Prime.factorization_self pb, Prime.factorization pa, hab] using h b

alias ord_compl_dvd_ord_compl_iff_dvd := ordCompl_dvd_ordCompl_iff_dvd

theorem dvd_iff_prime_pow_dvd_dvd (n d : ℕ) :
    d ∣ n ↔ ∀ p k : ℕ, Prime p → p ^ k ∣ d → p ^ k ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases eq_or_ne d 0 with (rfl | hd)
  · simp only [zero_dvd_iff, hn, false_iff, not_forall]
    exact ⟨2, n, prime_two, dvd_zero _, mt (le_of_dvd hn.bot_lt) (lt_two_pow n).not_le⟩
  refine ⟨fun h p k _ hpkd => dvd_trans hpkd h, ?_⟩
  rw [← factorization_prime_le_iff_dvd hd hn]
  intro h p pp
  simp_rw [← pp.pow_dvd_iff_le_factorization hn]
  exact h p _ pp (ordProj_dvd _ _)

theorem prod_primeFactors_dvd (n : ℕ) : ∏ p ∈ n.primeFactors, p ∣ n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · simpa [prod_primeFactorsList hn] using (n.primeFactorsList : Multiset ℕ).toFinset_prod_dvd_prod

-- DISSOLVED: factorization_gcd

-- DISSOLVED: factorization_lcm

variable (a b)

@[simp]
lemma factorizationLCMLeft_zero_left : factorizationLCMLeft 0 b = 1 := by
  simp [factorizationLCMLeft]

@[simp]
lemma factorizationLCMLeft_zero_right : factorizationLCMLeft a 0 = 1 := by
  simp [factorizationLCMLeft]

@[simp]
lemma factorizationLCRight_zero_left : factorizationLCMRight 0 b = 1 := by
  simp [factorizationLCMRight]

@[simp]
lemma factorizationLCMRight_zero_right : factorizationLCMRight a 0 = 1 := by
  simp [factorizationLCMRight]

lemma factorizationLCMLeft_pos :
    0 < factorizationLCMLeft a b := by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMLeft, Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p ≤ a.factorization p
  · simp only [h, reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2
  · simp only [h, reduceIte, one_ne_zero] at H

lemma factorizationLCMRight_pos :
    0 < factorizationLCMRight a b := by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMRight, Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p ≤ a.factorization p
  · simp only [h, reduceIte, pow_eq_zero_iff', ne_eq, reduceCtorEq] at H
  · simp only [h, ↓reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2

lemma coprime_factorizationLCMLeft_factorizationLCMRight :
    (factorizationLCMLeft a b).Coprime (factorizationLCMRight a b) := by
  rw [factorizationLCMLeft, factorizationLCMRight]
  refine coprime_prod_left_iff.mpr fun p hp ↦ coprime_prod_right_iff.mpr fun q hq ↦ ?_
  dsimp only; split_ifs with h h'
  any_goals simp only [coprime_one_right_eq_true, coprime_one_left_eq_true]
  refine coprime_pow_primes _ _ (prime_of_mem_primeFactors hp) (prime_of_mem_primeFactors hq) ?_
  contrapose! h'; rwa [← h']

variable {a b}

-- DISSOLVED: factorizationLCMLeft_mul_factorizationLCMRight

variable (a b)

lemma factorizationLCMLeft_dvd_left : factorizationLCMLeft a b ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [dvd_zero]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [factorizationLCMLeft]
  nth_rewrite 2 [← factorization_prod_pow_eq_self ha]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply prod_dvd_prod_of_dvd; rintro p -; dsimp only; split_ifs with le
    · rw [factorization_lcm ha hb]; apply pow_dvd_pow; exact sup_le le_rfl le
    · apply one_dvd
  · intro p hp; rw [mem_support_iff] at hp ⊢
    rw [factorization_lcm ha hb]; exact (lt_sup_iff.mpr <| .inl <| Nat.pos_of_ne_zero hp).ne'
  · intros; rw [pow_zero]

lemma factorizationLCMRight_dvd_right : factorizationLCMRight a b ∣ b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [factorizationLCMRight]
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [dvd_zero]
  nth_rewrite 2 [← factorization_prod_pow_eq_self hb]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply Finset.prod_dvd_prod_of_dvd; rintro p -; dsimp only; split_ifs with le
    · apply one_dvd
    · rw [factorization_lcm ha hb]; apply pow_dvd_pow; exact sup_le (not_le.1 le).le le_rfl
  · intro p hp; rw [mem_support_iff] at hp ⊢
    rw [factorization_lcm ha hb]; exact (lt_sup_iff.mpr <| .inr <| Nat.pos_of_ne_zero hp).ne'
  · intros; rw [pow_zero]

@[to_additive sum_primeFactors_gcd_add_sum_primeFactors_mul]
theorem prod_primeFactors_gcd_mul_prod_primeFactors_mul {β : Type*} [CommMonoid β] (m n : ℕ)
    (f : ℕ → β) :
    (m.gcd n).primeFactors.prod f * (m * n).primeFactors.prod f =
      m.primeFactors.prod f * n.primeFactors.prod f := by
  obtain rfl | hm₀ := eq_or_ne m 0
  · simp
  obtain rfl | hn₀ := eq_or_ne n 0
  · simp
  · rw [primeFactors_mul hm₀ hn₀, primeFactors_gcd hm₀ hn₀, mul_comm, Finset.prod_union_inter]

-- DISSOLVED: setOf_pow_dvd_eq_Icc_factorization

theorem Icc_factorization_eq_pow_dvd (n : ℕ) {p : ℕ} (pp : Prime p) :
    Icc 1 (n.factorization p) = {i ∈ Ico 1 n | p ^ i ∣ n} := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  ext x
  simp only [mem_Icc, Finset.mem_filter, mem_Ico, and_assoc, and_congr_right_iff,
    pp.pow_dvd_iff_le_factorization hn, iff_and_self]
  exact fun _ H => lt_of_le_of_lt H (factorization_lt p hn)

theorem factorization_eq_card_pow_dvd (n : ℕ) {p : ℕ} (pp : p.Prime) :
    n.factorization p = #{i ∈ Ico 1 n | p ^ i ∣ n} := by
  simp [← Icc_factorization_eq_pow_dvd n pp]

-- DISSOLVED: Ico_filter_pow_dvd_eq

/-! ### Factorization and coprimes -/

theorem factorization_eq_of_coprime_left {p a b : ℕ} (hab : Coprime a b)
    (hpa : p ∈ a.primeFactorsList) : (a * b).factorization p = a.factorization p := by
  rw [factorization_mul_apply_of_coprime hab, ← primeFactorsList_count_eq,
    ← primeFactorsList_count_eq,
    count_eq_zero_of_not_mem (coprime_primeFactorsList_disjoint hab hpa), add_zero]

theorem factorization_eq_of_coprime_right {p a b : ℕ} (hab : Coprime a b)
    (hpb : p ∈ b.primeFactorsList) : (a * b).factorization p = b.factorization p := by
  rw [mul_comm]
  exact factorization_eq_of_coprime_left (coprime_comm.mp hab) hpb

-- DISSOLVED: eq_iff_prime_padicValNat_eq

-- DISSOLVED: prod_pow_prime_padicValNat

/-! ### Lemmas about factorizations of particular functions -/

theorem card_multiples (n p : ℕ) : #{e ∈ range n | p ∣ e + 1} = n / p := by
  induction' n with n hn
  · simp
  simp [Nat.succ_div, add_ite, add_zero, Finset.range_succ, filter_insert, apply_ite card,
    card_insert_of_not_mem, hn]

theorem Ioc_filter_dvd_card_eq_div (n p : ℕ) : #{x ∈ Ioc 0 n | p ∣ x} = n / p := by
  induction' n with n IH
  · simp
  -- TODO: Golf away `h1` after Yaël PRs a lemma asserting this
  have h1 : Ioc 0 n.succ = insert n.succ (Ioc 0 n) := by
    rcases n.eq_zero_or_pos with (rfl | hn)
    · simp
    simp_rw [← Ico_succ_succ, Ico_insert_right (succ_le_succ hn.le), Ico_succ_right]
  simp [Nat.succ_div, add_ite, add_zero, h1, filter_insert, apply_ite card, card_insert_eq_ite, IH,
    Finset.mem_filter, mem_Ioc, not_le.2 (lt_add_one n)]

-- DISSOLVED: card_multiples'

end Nat
