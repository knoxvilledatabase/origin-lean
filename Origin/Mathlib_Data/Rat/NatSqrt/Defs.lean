/-
Extracted from Data/Rat/NatSqrt/Defs.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
Rational approximation of the square root of a natural number.

See also `Mathlib.Data.Rat.NatSqrt.Real` for comparisons with the real square root.
-/

namespace Nat

def ratSqrt (x : ℕ) (prec : ℕ) : ℚ := ((x * prec ^ 2).sqrt : ℚ) / prec

theorem ratSqrt_nonneg (x prec : ℕ) : 0 ≤ ratSqrt x prec := by
  unfold ratSqrt
  positivity

theorem ratSqrt_sq_le (x : ℕ) {prec : ℕ} (h : 0 < prec) : (ratSqrt x prec) ^ 2 ≤ x := by
  unfold ratSqrt
  rw [div_pow, div_le_iff₀ (by positivity)]
  norm_cast
  exact sqrt_le' (x * prec ^ 2)

theorem lt_ratSqrt_add_inv_prec_sq (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    x < (ratSqrt x prec + 1 / prec) ^ 2 := by
  unfold ratSqrt
  rw [← mul_lt_mul_iff_of_pos_right (a := (prec ^ 2 : ℚ)) (by positivity)]
  rw [← mul_pow, add_mul]
  rw [div_mul_cancel₀, div_mul_cancel₀]
  · norm_cast
    exact lt_succ_sqrt' (x * prec ^ 2)
  all_goals norm_cast; positivity

end Nat
