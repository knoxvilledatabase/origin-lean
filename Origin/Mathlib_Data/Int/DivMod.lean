/-
Extracted from Data/Int/DivMod.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic lemmas about division and modulo for integers

-/

namespace Int

/-! ### `ediv` and `fdiv` -/

theorem mul_ediv_le_mul_ediv_assoc {a : Int} (ha : 0 ≤ a) (b : Int) {c : Int} (hc : 0 ≤ c) :
    a * (b / c) ≤ a * b / c := by
  obtain rfl | hlt : c = 0 ∨ 0 < c := by lia
  · simp
  · rw [Int.le_ediv_iff_mul_le hlt, Int.mul_assoc]
    exact Int.mul_le_mul_of_nonneg_left (Int.ediv_mul_le b (Int.ne_of_gt hlt)) ha
