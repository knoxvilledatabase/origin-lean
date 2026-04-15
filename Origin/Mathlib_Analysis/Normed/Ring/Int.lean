/-
Extracted from Analysis/Normed/Ring/Int.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The integers as normed ring

This file contains basic facts about the integers as normed ring.

Recall that `‖n‖` denotes the norm of `n` as real number.
This norm is always nonnegative, so we can bundle the norm together with this fact,
to obtain a term of type `NNReal` (the nonnegative real numbers).
The resulting nonnegative real number is denoted by `‖n‖₊`.
-/

namespace Int

theorem nnnorm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖₊ = 1 := by
  obtain rfl | rfl := units_eq_one_or e <;>
    simp only [Units.coe_neg_one, Units.val_one, nnnorm_neg, nnnorm_one]

theorem norm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖ = 1 := by
  rw [← coe_nnnorm, nnnorm_coe_units, NNReal.coe_one]
