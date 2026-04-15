/-
Extracted from Algebra/AddTorsor/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Torsors of additive group actions

Further results for torsors, that are not in `Mathlib/Algebra/AddTorsor/Defs.lean` to avoid
increasing imports there.
-/

open scoped Pointwise

section General

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

namespace Set

theorem singleton_vsub_self (p : P) : ({p} : Set P) -ᵥ {p} = {(0 : G)} := by
  rw [Set.singleton_vsub_singleton, vsub_self]

end Set

theorem vsub_left_cancel {p₁ p₂ p : P} (h : p₁ -ᵥ p = p₂ -ᵥ p) : p₁ = p₂ := by
  rwa [← sub_eq_zero, vsub_sub_vsub_cancel_right, vsub_eq_zero_iff_eq] at h
