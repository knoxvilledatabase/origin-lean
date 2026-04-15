/-
Extracted from Data/Nat/Cast/Field.lean
Genuine: 1 | Conflates: 0 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic.Common
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Cast of naturals into fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a field.

## Main results

 * `Nat.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/

namespace Nat

variable {α : Type*}

-- DISSOLVED: cast_div

theorem cast_div_div_div_cancel_right [DivisionSemiring α] [CharZero α] {m n d : ℕ}
    (hn : d ∣ n) (hm : d ∣ m) :
    (↑(m / d) : α) / (↑(n / d) : α) = (m : α) / n := by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [Nat.zero_dvd.1 hm]
  replace hd : (d : α) ≠ 0 := by norm_cast
  rw [cast_div hm, cast_div hn, div_div_div_cancel_right₀ hd] <;> exact hd

end Nat
