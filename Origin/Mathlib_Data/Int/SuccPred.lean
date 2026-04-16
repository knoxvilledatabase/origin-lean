/-
Extracted from Data/Int/SuccPred.lean
Genuine: 9 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.SuccPred

noncomputable section

/-!
# Successors and predecessors of integers

In this file, we show that `ℤ` is both an archimedean `SuccOrder` and an archimedean `PredOrder`.
-/

open Function Order

namespace Int

@[instance] abbrev instSuccOrder : SuccOrder ℤ :=
  { SuccOrder.ofSuccLeIff succ fun {_ _} => Iff.rfl with succ := succ }

instance instSuccAddOrder : SuccAddOrder ℤ := ⟨fun _ => rfl⟩

@[instance] abbrev instPredOrder : PredOrder ℤ where
  pred := pred
  pred_le _ := (sub_one_lt_of_le le_rfl).le
  min_of_le_pred ha := ((sub_one_lt_of_le le_rfl).not_le ha).elim
  le_pred_of_lt {_ _} := le_sub_one_of_lt

instance instPredSubOrder : PredSubOrder ℤ := ⟨fun _ => rfl⟩

theorem pos_iff_one_le {a : ℤ} : 0 < a ↔ 1 ≤ a :=
  Order.succ_le_iff.symm

protected theorem succ_iterate (a : ℤ) : ∀ n, succ^[n] a = a + n :=
  Order.succ_iterate a

protected theorem pred_iterate (a : ℤ) : ∀ n, pred^[n] a = a - n :=
  Order.pred_iterate a

instance : IsSuccArchimedean ℤ :=
  ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [succ_iterate, toNat_sub_of_le h, ← add_sub_assoc, add_sub_cancel_left]⟩⟩

instance : IsPredArchimedean ℤ :=
  ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [pred_iterate, toNat_sub_of_le h, sub_sub_cancel]⟩⟩

/-! ### Covering relation -/

protected theorem covBy_iff_succ_eq {m n : ℤ} : m ⋖ n ↔ m + 1 = n :=
  succ_eq_iff_covBy.symm

theorem sub_one_covBy (z : ℤ) : z - 1 ⋖ z :=
  Order.sub_one_covBy z

theorem covBy_add_one (z : ℤ) : z ⋖ z + 1 :=
  Order.covBy_add_one z

@[simp, norm_cast]
theorem natCast_covBy {a b : ℕ} : (a : ℤ) ⋖ b ↔ a ⋖ b := by
  rw [Order.covBy_iff_add_one_eq, Order.covBy_iff_add_one_eq]
  exact Int.natCast_inj

end Int

alias ⟨_, CovBy.intCast⟩ := Int.natCast_covBy
