/-
Extracted from Algebra/Order/Ring/Pow.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Bernoulli's inequality

In this file we prove several versions of Bernoulli's inequality.
Besides the standard version `1 + n * a ≤ (1 + a) ^ n`,
we also prove `a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n`,
which can be regarded as Bernoulli's inequality for `b / a` multiplied by `a ^ n`.

Also, we prove versions for different typeclass assumptions on the (semi)ring.
-/

variable {R : Type*}

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {a b : R}

lemma Commute.pow_add_mul_le_add_pow_of_sq_nonneg (Hcomm : Commute a b) (ha : 0 ≤ a)
    (Hsq : 0 ≤ b ^ 2) (Hsq' : 0 ≤ (a + b) ^ 2) (H : 0 ≤ 2 * a + b) :
    ∀ n : ℕ, a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n
  | 0 => by simp
  | 1 => by simp
  | 2 =>
    calc
      a ^ 2 + (2 : ℕ) * a ^ 1 * b ≤ a ^ 2 + (2 : ℕ) * a ^ 1 * b + b ^ 2 :=
        le_add_of_nonneg_right Hsq
      _ = (a + b) ^ 2 := by simp [sq, add_mul, mul_add, two_mul, Hcomm.eq, add_assoc]
  | n + 3 => by
    calc
      _ ≤ a ^ (n + 3) + ↑(n + 3) * a ^ (n + 2) * b +
            ((n + 1) * (b ^ 2 * (2 * a + b) * a ^ n) + a ^ (n + 1) * b ^ 2) :=
        le_add_of_nonneg_right <| by
          apply_rules [add_nonneg, mul_nonneg, Nat.cast_nonneg, pow_nonneg, zero_le_one]
      _ = (a + b) ^ 2 * (a ^ (n + 1) + ↑(n + 1) * a ^ n * b) := by
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ', add_mul, mul_add,
          two_mul, pow_zero, mul_one,
          Hcomm.eq, (n.cast_commute (_ : R)).symm.left_comm, mul_assoc, (Hcomm.pow_left _).eq,
          (Hcomm.pow_left _).left_comm, Hcomm.left_comm, ← @two_add_one_eq_three R, one_mul]
        abel
      _ ≤ (a + b) ^ 2 * (a + b) ^ (n + 1) := by
        gcongr
        apply Commute.pow_add_mul_le_add_pow_of_sq_nonneg <;> assumption
      _ = (a + b) ^ (n + 3) := by simp [pow_succ', mul_assoc]

lemma one_add_mul_le_pow_of_sq_nonneg (Hsq : 0 ≤ a ^ 2) (Hsq' : 0 ≤ (1 + a) ^ 2) (H : 0 ≤ 2 + a)
    (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n := by
  simpa using (Commute.one_left a).pow_add_mul_le_add_pow_of_sq_nonneg zero_le_one Hsq Hsq'
    (by simpa using H) n
