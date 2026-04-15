/-
Extracted from Order/Heyting/Regular.lean
Genuine: 11 of 12 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Heyting regular elements

This file defines Heyting regular elements, elements of a Heyting algebra that are their own double
complement, and proves that they form a Boolean algebra.

From a logic standpoint, this means that we can perform classical logic within intuitionistic logic
by simply double-negating all propositions. This is practical for synthetic computability theory.

## Main declarations

* `IsRegular`: `a` is Heyting-regular if `aᶜᶜ = a`.
* `Regular`: The subtype of Heyting-regular elements.
* `Regular.BooleanAlgebra`: Heyting-regular elements form a Boolean algebra.

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

set_option linter.unusedDecidableInType false

open Function

variable {α : Type*}

namespace Heyting

section Compl

variable [Compl α] {a : α}

def IsRegular (a : α) : Prop :=
  aᶜᶜ = a

protected theorem IsRegular.eq : IsRegular a → aᶜᶜ = a :=
  id

-- INSTANCE (free from Core): IsRegular.decidablePred

end Compl

section HeytingAlgebra

variable [HeytingAlgebra α] {a b : α}

theorem isRegular_bot : IsRegular (⊥ : α) := by rw [IsRegular, compl_bot, compl_top]

theorem isRegular_top : IsRegular (⊤ : α) := by rw [IsRegular, compl_top, compl_bot]

theorem IsRegular.inf (ha : IsRegular a) (hb : IsRegular b) : IsRegular (a ⊓ b) := by
  rw [IsRegular, compl_compl_inf_distrib, ha.eq, hb.eq]

theorem IsRegular.himp (ha : IsRegular a) (hb : IsRegular b) : IsRegular (a ⇨ b) := by
  rw [IsRegular, compl_compl_himp_distrib, ha.eq, hb.eq]

theorem isRegular_compl (a : α) : IsRegular aᶜ :=
  compl_compl_compl _

protected theorem IsRegular.disjoint_compl_left_iff (ha : IsRegular a) :
    Disjoint aᶜ b ↔ b ≤ a := by rw [← le_compl_iff_disjoint_left, ha.eq]

protected theorem IsRegular.disjoint_compl_right_iff (hb : IsRegular b) :
    Disjoint a bᶜ ↔ a ≤ b := by rw [← le_compl_iff_disjoint_right, hb.eq]

abbrev _root_.BooleanAlgebra.ofRegular (h : ∀ a : α, IsRegular (a ⊔ aᶜ)) : BooleanAlgebra α :=
  have : ∀ a : α, IsCompl a aᶜ := fun a =>
    ⟨disjoint_compl_right,
      codisjoint_iff.2 <| by rw [← (h a), compl_sup, inf_compl_eq_bot, compl_bot]⟩
  { ‹HeytingAlgebra α›,
    GeneralizedHeytingAlgebra.toDistribLattice with
    himp_eq := fun _ _ =>
      eq_of_forall_le_iff fun _ => le_himp_iff.trans (this _).le_sup_right_iff_inf_left_le.symm
    inf_compl_le_bot := fun _ => (this _).1.le_bot
    top_le_sup_compl := fun _ => (this _).2.top_le }

variable (α)

def Regular : Type _ :=
  { a : α // IsRegular a }

variable {α}

namespace Regular
