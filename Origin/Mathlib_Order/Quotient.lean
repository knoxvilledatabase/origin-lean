/-
Extracted from Order/Quotient.lean
Genuine: 6 of 12 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
### Order instances on quotients

We define a `Preorder` instance on a general `Quotient`, as the transitive closure of the
`x ≤ y ∨ x ≈ y` relation. This is the quotient object in the category of preorders.

We show that in the case of a linear order with `Set.OrdConnected` equivalence classes, this
relation is automatically transitive (we don't need to take the transitive closure), and gives a
`LinearOrder` structure on the quotient. In that case, the resulting order is sometimes called a
**condensation**.
-/

open Set

variable {α : Type*} {s : Setoid α}

namespace Quotient

section LE

variable [LE α]

-- INSTANCE (free from Core): :

theorem le_def {x y : α} :
    Quotient.mk s x ≤ Quotient.mk s y ↔ Relation.TransGen (fun x y ↦ x ≤ y ∨ x ≈ y) x y := .rfl

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [@Std.Total

-- INSTANCE (free from Core): :

end LE

section Preorder

variable [Preorder α]

theorem mk_monotone : Monotone (Quotient.mk s) :=
  fun _ _ h ↦ .single (.inl h)

theorem lift_monotone {α β : Type*} [Preorder α] {s : Setoid α} [Preorder β]
    (f : α → β) (hf : Monotone f) (H : ∀ x₁ x₂, x₁ ≈ x₂ → f x₁ = f x₂) :
    Monotone (Quotient.lift f H) := by
  intro x y h
  induction x using Quotient.inductionOn with | h x
  induction y using Quotient.inductionOn with | h y
  induction h
  on_goal 2 => rename_i IH; apply IH.trans
  all_goals
    rename_i h
    cases h with
    | inl h => exact hf h
    | inr h => exact (H _ _ h).le

end Preorder

section LinearOrder

variable [LinearOrder α] [H : ∀ x, OrdConnected (Quotient.mk s ⁻¹' {x})]

theorem mk_le_mk {x y : α} : Quotient.mk s x ≤ Quotient.mk s y ↔ x ≤ y ∨ x ≈ y := by
  rw [← propext_iff]
  revert x y
  apply congrFun₂ <| @Relation.transGen_eq_self α _ ⟨fun x y z h₁ h₂ ↦ ?_⟩
  cases h₁ <;> cases h₂ <;> rename_i h₁ h₂
  · exact .inl <| h₁.trans h₂
  · rw [or_iff_not_imp_left, not_le]
    rw [← Quotient.eq_iff_equiv] at *
    exact fun h ↦ ((H _).out h₂.symm rfl ⟨h.le, h₁⟩).trans h₂
  · rw [or_iff_not_imp_left, not_le]
    rw [← Quotient.eq_iff_equiv] at *
    exact fun h ↦ ((H _).out h₁.symm rfl ⟨h₂, h.le⟩).symm
  · exact .inr (_root_.trans h₁ h₂)

-- INSTANCE (free from Core): instLinearOrder

theorem mk_lt_mk {x y : α} : Quotient.mk s x < Quotient.mk s y ↔ x < y ∧ ¬ x ≈ y := by
  classical
  contrapose! +distrib
  rw [mk_le_mk, comm_of (· ≈ ·)]

theorem lt_of_mk_lt_mk {x y : α} (h : Quotient.mk s x < Quotient.mk s y) : x < y :=
  (mk_lt_mk.1 h).1

end LinearOrder

end Quotient
