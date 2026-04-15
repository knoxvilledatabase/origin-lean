/-
Extracted from Data/Nat/Size.lean
Genuine: 12 | Conflates: 0 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Bits

/-! Lemmas about `size`. -/

namespace Nat

/-! ### `shiftLeft` and `shiftRight` -/

section

theorem shiftLeft_eq_mul_pow (m) : ∀ n, m <<< n = m * 2 ^ n := shiftLeft_eq _

theorem shiftLeft'_tt_eq_mul_pow (m) : ∀ n, shiftLeft' true m n + 1 = (m + 1) * 2 ^ n
  | 0 => by simp [shiftLeft', pow_zero, Nat.one_mul]
  | k + 1 => by
    rw [shiftLeft', bit_val, Bool.toNat_true, add_assoc, ← Nat.mul_add_one,
      shiftLeft'_tt_eq_mul_pow m k, mul_left_comm, mul_comm 2, pow_succ]

end

-- DISSOLVED: shiftLeft'_ne_zero_left

-- DISSOLVED: shiftLeft'_tt_ne_zero

/-! ### `size` -/

@[simp]
theorem size_zero : size 0 = 0 := by simp [size]

-- DISSOLVED: size_bit

section

@[simp]
theorem size_one : size 1 = 1 :=
  show size (bit true 0) = 1 by rw [size_bit, size_zero]; exact Nat.one_ne_zero

end

-- DISSOLVED: size_shiftLeft'

-- DISSOLVED: size_shiftLeft

theorem lt_size_self (n : ℕ) : n < 2 ^ size n := by
  rw [← one_shiftLeft]
  have : ∀ {n}, n = 0 → n < 1 <<< (size n) := by simp
  refine binaryRec ?_ ?_ n
  · apply this rfl
  intro b n IH
  by_cases h : bit b n = 0
  · apply this h
  rw [size_bit h, shiftLeft_succ, shiftLeft_eq, one_mul]
  cases b <;> dsimp [bit] <;> omega

theorem size_le {m n : ℕ} : size m ≤ n ↔ m < 2 ^ n :=
  ⟨fun h => lt_of_lt_of_le (lt_size_self _) (pow_le_pow_of_le_right (by decide) h), by
    rw [← one_shiftLeft]
    induction m using binaryRec generalizing n with
    | z => simp
    | f b m IH =>
      intro h
      by_cases e : bit b m = 0
      · simp [e]
      rw [size_bit e]
      cases n with
      | zero => exact e.elim (Nat.eq_zero_of_le_zero (le_of_lt_succ h))
      | succ n =>
        apply succ_le_succ (IH _)
        apply Nat.lt_of_mul_lt_mul_left (a := 2)
        simp only [shiftLeft_succ] at *
        refine lt_of_le_of_lt ?_ h
        cases b <;> dsimp [bit] <;> omega⟩

theorem lt_size {m n : ℕ} : m < size n ↔ 2 ^ m ≤ n := by
  rw [← not_lt, Decidable.iff_not_comm, not_lt, size_le]

theorem size_pos {n : ℕ} : 0 < size n ↔ 0 < n := by rw [lt_size]; rfl

theorem size_eq_zero {n : ℕ} : size n = 0 ↔ n = 0 := by
  simpa [Nat.pos_iff_ne_zero, not_iff_not] using size_pos

theorem size_pow {n : ℕ} : size (2 ^ n) = n + 1 :=
  le_antisymm (size_le.2 <| Nat.pow_lt_pow_right (by decide) (lt_succ_self _))
    (lt_size.2 <| le_rfl)

theorem size_le_size {m n : ℕ} (h : m ≤ n) : size m ≤ size n :=
  size_le.2 <| lt_of_le_of_lt h (lt_size_self _)

theorem size_eq_bits_len (n : ℕ) : n.bits.length = n.size := by
  induction n using Nat.binaryRec' with
  | z => simp
  | f _ _ h ih =>
    rw [size_bit, bits_append_bit _ _ h]
    · simp [ih]
    · simpa [bit_eq_zero_iff]

end Nat
