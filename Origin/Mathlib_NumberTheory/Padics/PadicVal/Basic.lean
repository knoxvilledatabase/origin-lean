/-
Extracted from NumberTheory/Padics/PadicVal/Basic.lean
Genuine: 51 of 79 | Dissolved: 24 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Prime.Int

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in padicNorm.lean.

## Notations

This file uses the local notation `/.` for `Rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## Calculations with `p`-adic valuations

* `padicValNat_factorial`: Legendre's Theorem. The `p`-adic valuation of `n!` is the sum of the
quotients `n / p ^ i`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound
greater than `log p n`. See `Nat.Prime.multiplicity_factorial` for the same result but stated in the
language of prime multiplicity.

* `sub_one_mul_padicValNat_factorial`: Legendre's Theorem.  Taking (`p - 1`) times
the `p`-adic valuation of `n!` equals `n` minus the sum of base `p` digits of `n`.

* `padicValNat_choose`: Kummer's Theorem. The `p`-adic valuation of `n.choose k` is the number
of carries when `k` and `n - k` are added in base `p`. This sum is expressed over the finset
`Ico 1 b` where `b` is any bound greater than `log p n`. See `Nat.Prime.multiplicity_choose` for the
same result but stated in the language of prime multiplicity.

* `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`: Kummer's Theorem. Taking (`p - 1`) times the
`p`-adic valuation of the binomial `n` over `k` equals the sum of the digits of `k` plus the sum of
the digits of `n - k` minus the sum of digits of `n`, all base `p`.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

universe u

open Nat

open Rat

open multiplicity

namespace padicValNat

open multiplicity

variable {p : ℕ}

@[simp]
theorem self (hp : 1 < p) : padicValNat p p = 1 := by
  simp [padicValNat_def', zero_lt_one.trans hp, hp.ne']

theorem eq_zero_of_not_dvd {n : ℕ} (h : ¬p ∣ n) : padicValNat p n = 0 :=
  eq_zero_iff.2 <| Or.inr <| Or.inr h

open Nat.maxPowDiv

theorem maxPowDiv_eq_emultiplicity {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDiv n = emultiplicity p n := by
  apply (emultiplicity_eq_of_dvd_of_not_dvd (pow_dvd p n) _).symm
  intro h
  apply Nat.not_lt.mpr <| le_of_dvd hp hn h
  simp

theorem maxPowDiv_eq_multiplicity {p n : ℕ} (hp : 1 < p) (hn : 0 < n) (h : Finite p n) :
    p.maxPowDiv n = multiplicity p n := by
  exact_mod_cast h.emultiplicity_eq_multiplicity ▸ maxPowDiv_eq_emultiplicity hp hn

@[csimp]
theorem padicValNat_eq_maxPowDiv : @padicValNat = @maxPowDiv := by
  ext p n
  by_cases h : 1 < p ∧ 0 < n
  · rw [padicValNat_def' h.1.ne' h.2, maxPowDiv_eq_multiplicity h.1 h.2]
    exact Nat.multiplicity_finite_iff.2 ⟨h.1.ne', h.2⟩
  · simp only [not_and_or,not_gt_eq,Nat.le_zero] at h
    apply h.elim
    · intro h
      interval_cases p
      · simp [Classical.em]
      · dsimp [padicValNat, maxPowDiv]
        rw [go, if_neg]; simp
    · intro h
      simp [h]

end padicValNat

def padicValInt (p : ℕ) (z : ℤ) : ℕ :=
  padicValNat p z.natAbs

namespace padicValInt

open multiplicity

variable {p : ℕ}

-- DISSOLVED: of_ne_one_ne_zero

@[simp]
protected theorem zero : padicValInt p 0 = 0 := by simp [padicValInt]

@[simp]
protected theorem one : padicValInt p 1 = 0 := by simp [padicValInt]

@[simp]
theorem of_nat {n : ℕ} : padicValInt p n = padicValNat p n := by simp [padicValInt]

theorem self (hp : 1 < p) : padicValInt p p = 1 := by simp [padicValNat.self hp]

theorem eq_zero_of_not_dvd {z : ℤ} (h : ¬(p : ℤ) ∣ z) : padicValInt p z = 0 := by
  rw [padicValInt, padicValNat.eq_zero_iff]
  right; right
  rwa [← Int.ofNat_dvd_left]

end padicValInt

def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.den

lemma padicValRat_def (p : ℕ) (q : ℚ) :
    padicValRat p q = padicValInt p q.num - padicValNat p q.den :=
  rfl

namespace padicValRat

open multiplicity

variable {p : ℕ}

@[simp]
protected theorem neg (q : ℚ) : padicValRat p (-q) = padicValRat p q := by
  simp [padicValRat, padicValInt]

@[simp]
protected theorem zero : padicValRat p 0 = 0 := by simp [padicValRat]

@[simp]
protected theorem one : padicValRat p 1 = 0 := by simp [padicValRat]

@[simp]
theorem of_int {z : ℤ} : padicValRat p z = padicValInt p z := by simp [padicValRat]

-- DISSOLVED: of_int_multiplicity

-- DISSOLVED: multiplicity_sub_multiplicity

@[simp]
theorem of_nat {n : ℕ} : padicValRat p n = padicValNat p n := by simp [padicValRat]

theorem self (hp : 1 < p) : padicValRat p p = 1 := by simp [hp]

end padicValRat

section padicValNat

variable {p : ℕ}

theorem zero_le_padicValRat_of_nat (n : ℕ) : 0 ≤ padicValRat p n := by simp

@[norm_cast]
theorem padicValRat_of_nat (n : ℕ) : ↑(padicValNat p n) = padicValRat p n := by simp

@[simp]
theorem padicValNat_self [Fact p.Prime] : padicValNat p p = 1 := by
  rw [padicValNat_def (@Fact.out p.Prime).pos]
  simp

theorem one_le_padicValNat_of_dvd {n : ℕ} [hp : Fact p.Prime] (hn : 0 < n) (div : p ∣ n) :
    1 ≤ padicValNat p n := by
  rwa [← WithTop.coe_le_coe, ENat.some_eq_coe, padicValNat_eq_emultiplicity hn,
    ← pow_dvd_iff_le_emultiplicity, pow_one]

-- DISSOLVED: dvd_iff_padicValNat_ne_zero

end padicValNat

namespace padicValRat

open multiplicity

variable {p : ℕ} [hp : Fact p.Prime]

-- DISSOLVED: finite_int_prime_iff

-- DISSOLVED: defn

-- DISSOLVED: mul

-- DISSOLVED: pow

protected theorem inv (q : ℚ) : padicValRat p q⁻¹ = -padicValRat p q := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul (inv_ne_zero hq) hq, inv_mul_cancel₀ hq,
      padicValRat.one]

-- DISSOLVED: div

-- DISSOLVED: padicValRat_le_padicValRat_iff

-- DISSOLVED: le_padicValRat_add_of_le

-- DISSOLVED: min_le_padicValRat_add

-- DISSOLVED: add_eq_min

-- DISSOLVED: add_eq_of_lt

-- DISSOLVED: lt_add_of_lt

@[simp]
lemma self_pow_inv (r : ℕ) : padicValRat p ((p : ℚ) ^ r)⁻¹ = -r := by
  rw [padicValRat.inv, neg_inj, padicValRat.pow (Nat.cast_ne_zero.mpr hp.elim.ne_zero),
      padicValRat.self hp.elim.one_lt, mul_one]

-- DISSOLVED: sum_pos_of_pos

theorem lt_sum_of_lt {p j : ℕ} [hp : Fact (Nat.Prime p)] {F : ℕ → ℚ} {S : Finset ℕ}
    (hS : S.Nonempty) (hF : ∀ i, i ∈ S → padicValRat p (F j) < padicValRat p (F i))
    (hn1 : ∀ i : ℕ, 0 < F i) : padicValRat p (F j) < padicValRat p (∑ i ∈ S, F i) := by
  induction' hS using Finset.Nonempty.cons_induction with k s S' Hnot Hne Hind
  · rw [Finset.sum_singleton]
    exact hF k (by simp)
  · rw [Finset.cons_eq_insert, Finset.sum_insert Hnot]
    exact padicValRat.lt_add_of_lt
      (ne_of_gt (add_pos (hn1 s) (Finset.sum_pos (fun i _ => hn1 i) Hne)))
      (hF _ (by simp [Finset.mem_insert, true_or]))
      (Hind (fun i hi => hF _ (by rw [Finset.cons_eq_insert,Finset.mem_insert]; exact Or.inr hi)))

end padicValRat

namespace padicValNat

variable {p a b : ℕ} [hp : Fact p.Prime]

-- DISSOLVED: mul

protected theorem div_of_dvd (h : b ∣ a) :
    padicValNat p (a / b) = padicValNat p a - padicValNat p b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  rw [mul_comm, k.mul_div_cancel hb.bot_lt, padicValNat.mul hk hb, Nat.add_sub_cancel]

protected theorem div (dvd : p ∣ b) : padicValNat p (b / p) = padicValNat p b - 1 := by
  rw [padicValNat.div_of_dvd dvd, padicValNat_self]

-- DISSOLVED: pow

@[simp]
protected theorem prime_pow (n : ℕ) : padicValNat p (p ^ n) = n := by
  rw [padicValNat.pow _ (@Fact.out p.Prime).ne_zero, padicValNat_self, mul_one]

protected theorem div_pow (dvd : p ^ a ∣ b) : padicValNat p (b / p ^ a) = padicValNat p b - a := by
  rw [padicValNat.div_of_dvd dvd, padicValNat.prime_pow]

protected theorem div' {m : ℕ} (cpm : Coprime p m) {b : ℕ} (dvd : m ∣ b) :
    padicValNat p (b / m) = padicValNat p b := by
  rw [padicValNat.div_of_dvd dvd, eq_zero_of_not_dvd (hp.out.coprime_iff_not_dvd.mp cpm),
    Nat.sub_zero]

end padicValNat

section padicValNat

variable {p : ℕ}

theorem dvd_of_one_le_padicValNat {n : ℕ} (hp : 1 ≤ padicValNat p n) : p ∣ n := by
  by_contra h
  rw [padicValNat.eq_zero_of_not_dvd h] at hp
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp)

theorem pow_padicValNat_dvd {n : ℕ} : p ^ padicValNat p n ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hn); · simp
  rcases eq_or_ne p 1 with (rfl | hp); · simp
  apply pow_dvd_of_le_multiplicity
  rw [padicValNat_def'] <;> assumption

-- DISSOLVED: padicValNat_dvd_iff_le

theorem padicValNat_dvd_iff (n : ℕ) [hp : Fact p.Prime] (a : ℕ) :
    p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact iff_of_true (dvd_zero _) (Or.inl rfl)
  · rw [padicValNat_dvd_iff_le ha, or_iff_right ha]

-- DISSOLVED: pow_succ_padicValNat_not_dvd

theorem padicValNat_primes {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (neq : p ≠ q) :
    padicValNat p q = 0 :=
  @padicValNat.eq_zero_of_not_dvd p q <|
    (not_congr (Iff.symm (prime_dvd_prime_iff_eq hp.1 hq.1))).mp neq

theorem padicValNat_prime_prime_pow {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n : ℕ) (neq : p ≠ q) : padicValNat p (q ^ n) = 0 := by
  rw [padicValNat.pow _ <| Nat.Prime.ne_zero hq.elim, padicValNat_primes neq, mul_zero]

theorem padicValNat_mul_pow_left {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : ℕ) (neq : p ≠ q) : padicValNat p (p^n * q^m) = n := by
  rw [padicValNat.mul (NeZero.ne' (p^n)).symm (NeZero.ne' (q^m)).symm,
    padicValNat.prime_pow, padicValNat_prime_prime_pow m neq, add_zero]

theorem padicValNat_mul_pow_right {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : ℕ) (neq : q ≠ p) : padicValNat q (p^n * q^m) = m := by
  rw [mul_comm (p^n) (q^m)]
  exact padicValNat_mul_pow_left m n neq

lemma padicValNat_le_nat_log (n : ℕ) : padicValNat p n ≤ Nat.log p n := by
  rcases n with _ | n
  · simp
  rcases p with _ | _ | p
  · simp
  · simp
  exact Nat.le_log_of_pow_le p.one_lt_succ_succ (le_of_dvd n.succ_pos pow_padicValNat_dvd)

lemma nat_log_eq_padicValNat_iff {n : ℕ} [hp : Fact (Nat.Prime p)] (hn : 0 < n) :
    Nat.log p n = padicValNat p n ↔ n < p ^ (padicValNat p n + 1) := by
  rw [Nat.log_eq_iff (Or.inr ⟨(Nat.Prime.one_lt' p).out, by omega⟩), and_iff_right_iff_imp]
  exact fun _ => Nat.le_of_dvd hn pow_padicValNat_dvd

-- DISSOLVED: Nat.log_ne_padicValNat_succ

lemma Nat.max_log_padicValNat_succ_eq_log_succ (n : ℕ) :
    max (log 2 n) (padicValNat 2 (n + 1)) = log 2 (n + 1) := by
  apply le_antisymm (max_le (le_log_of_pow_le one_lt_two (pow_log_le_add_one 2 n))
    (padicValNat_le_nat_log (n + 1)))
  rw [le_max_iff, or_iff_not_imp_left, not_le]
  intro h
  replace h := le_antisymm (add_one_le_iff.mpr (lt_pow_of_log_lt one_lt_two h))
    (pow_log_le_self 2 n.succ_ne_zero)
  rw [h, padicValNat.prime_pow, ← h]

-- DISSOLVED: range_pow_padicValNat_subset_divisors

theorem range_pow_padicValNat_subset_divisors' {n : ℕ} [hp : Fact p.Prime] :
    ((Finset.range (padicValNat p n)).image fun t => p ^ (t + 1)) ⊆ n.divisors.erase 1 := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  intro t ht
  simp only [exists_prop, Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_erase, Nat.mem_divisors]
  refine ⟨?_, (pow_dvd_pow p <| succ_le_iff.2 hk).trans pow_padicValNat_dvd, hn⟩
  exact (Nat.one_lt_pow k.succ_ne_zero hp.out.one_lt).ne'

theorem padicValNat_factorial_mul (n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * n) ! = padicValNat p n ! + n := by
  apply Nat.cast_injective (R := ℕ∞)
  rw [padicValNat_eq_emultiplicity <| factorial_pos (p * n), Nat.cast_add,
      padicValNat_eq_emultiplicity <| factorial_pos n]
  exact Prime.emultiplicity_factorial_mul hp.out

theorem padicValNat_eq_zero_of_mem_Ioo {m k : ℕ}
    (hm : m ∈ Set.Ioo (p * k) (p * (k + 1))) : padicValNat p m = 0 :=
  padicValNat.eq_zero_of_not_dvd <| not_dvd_of_between_consec_multiples hm.1 hm.2

theorem padicValNat_factorial_mul_add {n : ℕ} (m : ℕ) [hp : Fact p.Prime] (h : n < p) :
    padicValNat p (p * m + n) ! = padicValNat p (p * m) ! := by
  induction n with
  | zero => rw [add_zero]
  | succ n hn =>
    rw [add_succ, factorial_succ,
      padicValNat.mul (succ_ne_zero (p * m + n)) <| factorial_ne_zero (p * m + _),
      hn <| lt_of_succ_lt h, ← add_succ,
      padicValNat_eq_zero_of_mem_Ioo ⟨(Nat.lt_add_of_pos_right <| succ_pos n),
        (Nat.mul_add _ _ _▸ Nat.mul_one _ ▸ ((add_lt_add_iff_left (p * m)).mpr h))⟩,
      zero_add]

@[simp] theorem padicValNat_mul_div_factorial (n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * (n / p))! = padicValNat p n ! := by
  nth_rw 2 [← div_add_mod n p]
  exact (padicValNat_factorial_mul_add (n / p) <| mod_lt n hp.out.pos).symm

theorem padicValNat_factorial {n b : ℕ} [hp : Fact p.Prime] (hnb : log p n < b) :
    padicValNat p (n !) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  exact_mod_cast ((padicValNat_eq_emultiplicity (p := p) <| factorial_pos _) ▸
      Prime.emultiplicity_factorial hp.out hnb)

theorem sub_one_mul_padicValNat_factorial [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (n !) = n - (p.digits n).sum := by
  rw [padicValNat_factorial <| lt_succ_of_lt <| lt.base (log p n)]
  nth_rw 2 [← zero_add 1]
  rw [Nat.succ_eq_add_one, ← Finset.sum_Ico_add' _ 0 _ 1,
    Ico_zero_eq_range, ← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits, Nat.succ_eq_add_one]

theorem padicValNat_choose {n k b : ℕ} [hp : Fact p.Prime] (hkn : k ≤ n) (hnb : log p n < b) :
    padicValNat p (choose n k) =
    ((Finset.Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| choose_pos hkn) ▸
    Prime.emultiplicity_choose hp.out hkn hnb

theorem padicValNat_choose' {n k b : ℕ} [hp : Fact p.Prime] (hnb : log p (n + k) < b) :
    padicValNat p (choose (n + k) k) =
    ((Finset.Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + n % p ^ i).card := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| choose_pos <|
    Nat.le_add_left k n)▸ Prime.emultiplicity_choose' hp.out hnb

theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits' {k n : ℕ} [hp : Fact p.Prime] :
    (p - 1) * padicValNat p (choose (n + k) k) =
    (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum := by
  have h : k ≤ n + k := by exact Nat.le_add_left k n
  simp only [Nat.choose_eq_factorial_div_factorial h]
  rw [padicValNat.div_of_dvd <| factorial_mul_factorial_dvd_factorial h, Nat.mul_sub_left_distrib,
      padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _), Nat.mul_add]
  simp only [sub_one_mul_padicValNat_factorial]
  rw [← Nat.sub_add_comm <| digit_sum_le p k, Nat.add_sub_cancel n k, ← Nat.add_sub_assoc <|
      digit_sum_le p n, Nat.sub_sub (k + n), ← Nat.sub_right_comm, Nat.sub_sub, sub_add_eq,
      add_comm, tsub_tsub_assoc (Nat.le_refl (k + n)) <| (add_comm k n) ▸ (Nat.add_le_add
      (digit_sum_le p n) (digit_sum_le p k)), Nat.sub_self (k + n), zero_add, add_comm]

theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits {k n : ℕ} [hp : Fact p.Prime]
    (h : k ≤ n) : (p - 1) * padicValNat p (choose n k) =
    (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum := by
  convert @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' _ _ _ ‹_›
  all_goals omega

end padicValNat

section padicValInt

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValInt_dvd_iff (n : ℕ) (a : ℤ) : (p : ℤ) ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValInt p a := by
  rw [padicValInt, ← Int.natAbs_eq_zero, ← padicValNat_dvd_iff, ← Int.natCast_dvd, Int.natCast_pow]

theorem padicValInt_dvd (a : ℤ) : (p : ℤ) ^ padicValInt p a ∣ a := by
  rw [padicValInt_dvd_iff]
  exact Or.inr le_rfl

theorem padicValInt_self : padicValInt p p = 1 :=
  padicValInt.self hp.out.one_lt

-- DISSOLVED: padicValInt.mul

-- DISSOLVED: padicValInt_mul_eq_succ

end padicValInt
