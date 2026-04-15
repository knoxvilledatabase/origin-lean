/-
Extracted from Algebra/Field/NegOnePow.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Integer powers of `-1` in a field -/

namespace Int

lemma cast_negOnePow (K : Type*) (n : ℤ) [DivisionRing K] : n.negOnePow = (-1 : K) ^ n := by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩
  · simp [zpow_mul, zpow_ofNat]
  · rw [zpow_add_one₀ (by simp), zpow_mul, zpow_ofNat]
    simp

end Int
