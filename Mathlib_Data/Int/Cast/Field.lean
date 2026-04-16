/-
Extracted from Data/Int/Cast/Field.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Int.Defs

noncomputable section

/-!
# Cast of integers into fields

This file concerns the canonical homomorphism `ℤ → F`, where `F` is a field.

## Main results

 * `Int.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/

namespace Int

open Nat

variable {α : Type*}

@[norm_cast]
theorem cast_neg_natCast {R} [DivisionRing R] (n : ℕ) : ((-n : ℤ) : R) = -n := by simp

@[simp]
theorem cast_div [DivisionRing α] {m n : ℤ} (n_dvd : n ∣ m) (hn : (n : α) ≠ 0) :
    ((m / n : ℤ) : α) = m / n := by
  rcases n_dvd with ⟨k, rfl⟩
  have : n ≠ 0 := by rintro rfl; simp at hn
  rw [Int.mul_ediv_cancel_left _ this, mul_comm n, Int.cast_mul, mul_div_cancel_right₀ _ hn]

end Int
