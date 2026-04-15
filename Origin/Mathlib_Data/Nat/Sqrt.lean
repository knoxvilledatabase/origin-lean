/-
Extracted from Data/Nat/Sqrt.lean
Genuine: 16 of 16 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Properties of the natural number square root function.
-/

namespace Nat

assert_not_exists Monoid

variable {m n a : ℕ}

/-!
### `sqrt`

See [Wikipedia, *Methods of computing square roots*]
(https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)).
-/

private lemma iter_fp_bound (n k : ℕ) :
    let iter_next (n guess : ℕ) := (guess + n / guess) / 2;
    sqrt.iter n k ≤ iter_next n (sqrt.iter n k) := by
  intro iter_next
  unfold sqrt.iter
  if h : (k + n / k) / 2 < k then
    simpa [if_pos h] using iter_fp_bound _ _
  else
    grind

private lemma AM_GM : {a b : ℕ} → (4 * a * b ≤ (a + b) * (a + b))
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact zero_le _
  | a + 1, b + 1 => by
    simpa only [Nat.mul_add, Nat.add_mul, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left]
      using Nat.add_le_add_right (@AM_GM a b) 4

lemma sqrt.iter_sq_le (n guess : ℕ) : sqrt.iter n guess * sqrt.iter n guess ≤ n := by
  unfold sqrt.iter
  let next := (guess + n / guess) / 2
  if h : next < guess then
    simpa only [next, dif_pos h] using sqrt.iter_sq_le n next
  else
    apply Nat.mul_le_of_le_div
    grind

lemma sqrt.lt_iter_succ_sq (n guess : ℕ) (hn : n < (guess + 1) * (guess + 1)) :
    n < (sqrt.iter n guess + 1) * (sqrt.iter n guess + 1) := by
  unfold sqrt.iter
  -- m was `next`
  let m := (guess + n / guess) / 2
  dsimp
  split_ifs with h
  · suffices n < (m + 1) * (m + 1) by
      simpa only [dif_pos h] using sqrt.lt_iter_succ_sq n m this
    refine Nat.lt_of_mul_lt_mul_left ?_ (a := 4 * (guess * guess))
    apply Nat.lt_of_le_of_lt AM_GM
    rw [show (4 : ℕ) = 2 * 2 from rfl]
    rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    refine Nat.mul_self_lt_mul_self (?_ : _ < _ * ((_ / 2) + 1))
    rw [← add_div_right _ (by decide), Nat.mul_comm 2, Nat.mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux_lemma {a : ℕ} : a ≤ 2 * ((a + 1) / 2) := by lia
    refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ aux_lemma)
    rw [Nat.add_assoc, Nat.mul_add]
    exact Nat.add_lt_add_left (lt_mul_div_succ _ (lt_of_le_of_lt (Nat.zero_le m) h)) _
  · exact hn

private def IsSqrt (n q : ℕ) : Prop :=
  q * q ≤ n ∧ n < (q + 1) * (q + 1)

private lemma sqrt_isSqrt (n : ℕ) : IsSqrt n (sqrt n) := by
  match n with
  | 0 => simp [IsSqrt, sqrt]
  | 1 => simp [IsSqrt, sqrt]
  | n + 2 =>
    have h : ¬ (n + 2) ≤ 1 := by simp
    simp only [IsSqrt, sqrt, h, ite_false]
    refine ⟨sqrt.iter_sq_le _ _, sqrt.lt_iter_succ_sq _ _ ?_⟩
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← Nat.add_assoc]
    rw [Nat.lt_add_one_iff, Nat.add_assoc, ← Nat.mul_two]
    refine le_trans (Nat.le_of_eq (div_add_mod' (n + 2) 2).symm) ?_
    rw [show (n + 2) / 2 * 2 + (n + 2) % 2 = n + 2 by grind]
    simp only [shiftLeft_eq, Nat.one_mul]
    refine Nat.le_of_lt (Nat.le_trans lt_log2_self (le_add_right_of_le ?_))
    rw [← Nat.pow_add]
    grind

lemma sqrt_le (n : ℕ) : sqrt n * sqrt n ≤ n := (sqrt_isSqrt n).left

lemma sqrt_le' (n : ℕ) : sqrt n ^ 2 ≤ n := by simpa [Nat.pow_two] using sqrt_le n

lemma lt_succ_sqrt (n : ℕ) : n < succ (sqrt n) * succ (sqrt n) := (sqrt_isSqrt n).right

lemma lt_succ_sqrt' (n : ℕ) : n < succ (sqrt n) ^ 2 := by simpa [Nat.pow_two] using lt_succ_sqrt n

lemma sqrt_le_add (n : ℕ) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)

lemma le_sqrt : m ≤ sqrt n ↔ m * m ≤ n :=
  ⟨fun h ↦ le_trans (mul_self_le_mul_self h) (sqrt_le n),
    fun h ↦ le_of_lt_succ <| Nat.mul_self_lt_mul_self_iff.1 <| lt_of_le_of_lt h (lt_succ_sqrt n)⟩

lemma le_sqrt' : m ≤ sqrt n ↔ m ^ 2 ≤ n := by simpa only [Nat.pow_two] using le_sqrt

lemma sqrt_lt : sqrt m < n ↔ m < n * n := by simp only [← not_le, le_sqrt]

lemma sqrt_lt' : sqrt m < n ↔ m < n ^ 2 := by simp only [← not_le, le_sqrt']

lemma sqrt_le_self (n : ℕ) : sqrt n ≤ n := le_trans (le_mul_self _) (sqrt_le n)
