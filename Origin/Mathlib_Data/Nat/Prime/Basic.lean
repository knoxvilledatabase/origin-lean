/-
Extracted from Data/Nat/Prime/Basic.lean
Genuine: 24 of 28 | Dissolved: 2 | Infrastructure: 2
-/
import Origin.Core

/-!
# Prime numbers

This file develops the theory of prime numbers: natural numbers `p ≥ 2` whose only divisors are
`p` and `1`.

-/

namespace Nat

variable {n : ℕ}

theorem prime_mul_iff {a b : ℕ} : Nat.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime ∧ a = 1 := by
  simp only [irreducible_mul_iff, ← irreducible_iff_nat_prime, Nat.isUnit_iff]

theorem not_prime_mul {a b : ℕ} (a1 : a ≠ 1) (b1 : b ≠ 1) : ¬Prime (a * b) := by
  simp [prime_mul_iff, *]

theorem Prime.dvd_iff_eq {p a : ℕ} (hp : p.Prime) (a1 : a ≠ 1) : a ∣ p ↔ p = a := by
  refine ⟨?_, by rintro rfl; rfl⟩
  rintro ⟨j, rfl⟩
  rcases prime_mul_iff.mp hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact mul_one _
  · exact (a1 rfl).elim

theorem Prime.eq_two_or_odd {p : ℕ} (hp : Prime p) : p = 2 ∨ p % 2 = 1 :=
  p.mod_two_eq_zero_or_one.imp_left fun h =>
    ((hp.eq_one_or_self_of_dvd 2 (dvd_of_mod_eq_zero h)).resolve_left (by decide)).symm

theorem Prime.eq_two_or_odd' {p : ℕ} (hp : Prime p) : p = 2 ∨ Odd p :=
  Or.imp_right (fun h => ⟨p / 2, (div_add_mod p 2).symm.trans (congr_arg _ h)⟩) hp.eq_two_or_odd

theorem Prime.five_le_of_ne_two_of_ne_three {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2)
    (h_three : p ≠ 3) : 5 ≤ p := by
  by_contra! h
  revert h_two h_three hp
  decide +revert

end

theorem Prime.pred_pos {p : ℕ} (pp : Prime p) : 0 < pred p :=
  lt_pred_iff.2 pp.one_lt

theorem succ_pred_prime {p : ℕ} (pp : Prime p) : succ (pred p) = p :=
  succ_pred_eq_of_pos pp.pos

theorem exists_dvd_of_not_prime {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
  ⟨minFac n, minFac_dvd _, ne_of_gt (minFac_prime (ne_of_gt n2)).one_lt,
    ne_of_lt <| (not_prime_iff_minFac_lt n2).1 np⟩

theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) :
    ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
  ⟨minFac n, minFac_dvd _, (minFac_prime (ne_of_gt n2)).two_le,
    (not_prime_iff_minFac_lt n2).1 np⟩

theorem not_prime_of_dvd_of_ne {m n : ℕ} (h1 : m ∣ n) (h2 : m ≠ 1) (h3 : m ≠ n) : ¬Prime n :=
  fun h => Or.elim (h.eq_one_or_self_of_dvd m h1) h2 h3

theorem not_prime_of_dvd_of_lt {m n : ℕ} (h1 : m ∣ n) (h2 : 2 ≤ m) (h3 : m < n) : ¬Prime n :=
  not_prime_of_dvd_of_ne h1 (ne_of_gt h2) (ne_of_lt h3)

theorem not_prime_iff_exists_dvd_ne {n : ℕ} (h : 2 ≤ n) : (¬Prime n) ↔ ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
  ⟨exists_dvd_of_not_prime h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_ne h1 h2 h3⟩

theorem not_prime_iff_exists_dvd_lt {n : ℕ} (h : 2 ≤ n) : (¬Prime n) ↔ ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
  ⟨exists_dvd_of_not_prime2 h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_lt h1 h2 h3⟩

theorem not_prime_iff_exists_mul_eq {n : ℕ} (h : 2 ≤ n) :
    (¬Prime n) ↔ ∃ a b, a < n ∧ b < n ∧ a * b = n := by
  rw [prime_iff_not_exists_mul_eq, and_iff_right h, Classical.not_not]

theorem dvd_of_forall_prime_mul_dvd {a b : ℕ}
    (hdvd : ∀ p : ℕ, p.Prime → p ∣ a → p * a ∣ b) : a ∣ b := by
  obtain rfl | ha := eq_or_ne a 1
  · apply one_dvd
  obtain ⟨p, hp⟩ := exists_prime_and_dvd ha
  exact _root_.trans (dvd_mul_left a p) (hdvd p hp.1 hp.2)

theorem Prime.even_iff {p : ℕ} (hp : Prime p) : Even p ↔ p = 2 := by
  rw [even_iff_two_dvd, prime_dvd_prime_iff_eq prime_two hp, eq_comm]

theorem Prime.odd_iff {p : ℕ} (hp : Prime p) : Odd p ↔ 3 ≤ p := by
  rw [← not_iff_not, not_odd_iff_even, hp.even_iff, not_le]
  grind [hp.two_le]

theorem Prime.odd_of_ne_two {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2) : Odd p :=
  hp.eq_two_or_odd'.resolve_left h_two

theorem Prime.even_sub_one {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : Even (p - 1) :=
  let ⟨n, hn⟩ := hp.odd_of_ne_two h2; ⟨n, by rw [hn, Nat.add_sub_cancel, two_mul]⟩

theorem Prime.mod_two_eq_one_iff_ne_two {p : ℕ} (hp : p.Prime) : p % 2 = 1 ↔ p ≠ 2 := by
  refine ⟨fun h hf => ?_, hp.eq_two_or_odd.resolve_left⟩
  rw [hf] at h
  simp at h

theorem coprime_of_dvd' {m n : ℕ} (H : ∀ k, Prime k → k ∣ m → k ∣ n → k ∣ 1) : Coprime m n :=
  coprime_of_dvd fun k kp km kn => not_le_of_gt kp.one_lt <| le_of_dvd Nat.one_pos <| H k kp km kn

theorem Prime.dvd_iff_not_coprime {p n : ℕ} (pp : Prime p) : p ∣ n ↔ ¬Coprime p n :=
  iff_not_comm.2 pp.coprime_iff_not_dvd

-- DISSOLVED: coprime_of_lt_minFac

-- DISSOLVED: gcd_eq_one_of_lt_minFac

theorem Prime.not_dvd_mul {p m n : ℕ} (pp : Prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n) : ¬p ∣ m * n :=
  mt pp.dvd_mul.1 <| by simp [Hm, Hn]
