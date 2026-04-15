/-
Extracted from Data/Int/ConditionallyCompleteOrder.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/

open Int

noncomputable section

open scoped Classical in

-- INSTANCE (free from Core): instConditionallyCompleteLinearOrder

namespace Int

theorem csSup_eq_greatestOfBdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b)
    (Hinh : ∃ z : ℤ, z ∈ s) : sSup s = greatestOfBdd b Hb Hinh := by
  have : s.Nonempty ∧ BddAbove s := ⟨Hinh, b, Hb⟩
  simp only [sSup, dif_pos this]
  convert (coe_greatestOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddAbove s)) Hinh).symm
