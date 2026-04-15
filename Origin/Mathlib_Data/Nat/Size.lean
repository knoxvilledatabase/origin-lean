/-
Extracted from Data/Nat/Size.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! Lemmas about `size`. -/

namespace Nat

/-! ### `shiftLeft` and `shiftRight` -/

theorem shiftLeft_eq_mul_pow (m) : ∀ n, m <<< n = m * 2 ^ n := shiftLeft_eq _

theorem shiftLeft'_true_eq_mul_pow (m) : ∀ n, shiftLeft' true m n + 1 = (m + 1) * 2 ^ n
  | 0 => by simp [shiftLeft', Nat.pow_zero]
  | k + 1 => by
    rw [shiftLeft', bit_val, Bool.toNat_true, Nat.add_assoc, ← Nat.mul_add_one,
      shiftLeft'_true_eq_mul_pow m k, Nat.mul_left_comm, Nat.mul_comm 2, Nat.pow_succ]
