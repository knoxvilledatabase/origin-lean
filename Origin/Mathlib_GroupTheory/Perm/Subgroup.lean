/-
Extracted from GroupTheory/Perm/Subgroup.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic

/-!
# Lemmas about subgroups within the permutations (self-equivalences) of a type `α`

This file provides extra lemmas about some `Subgroup`s that exist within `Equiv.Perm α`.
`GroupTheory.Subgroup` depends on `GroupTheory.Perm.Basic`, so these need to be in a separate
file.

It also provides decidable instances on membership in these subgroups, since
`MonoidHom.decidableMemRange` cannot be inferred without the help of a lambda.
The presence of these instances induces a `Fintype` instance on the `QuotientGroup.Quotient` of
these subgroups.
-/

namespace Equiv

namespace Perm

universe u

instance sumCongrHom.decidableMemRange {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] : DecidablePred (· ∈ (sumCongrHom α β).range) := fun _ => inferInstance

@[simp]
theorem sumCongrHom.card_range {α β : Type*} [Fintype (sumCongrHom α β).range]
    [Fintype (Perm α × Perm β)] :
    Fintype.card (sumCongrHom α β).range = Fintype.card (Perm α × Perm β) :=
  Fintype.card_eq.mpr ⟨(ofInjective (sumCongrHom α β) sumCongrHom_injective).symm⟩

instance sigmaCongrRightHom.decidableMemRange {α : Type*} {β : α → Type*} [DecidableEq α]
    [∀ a, DecidableEq (β a)] [Fintype α] [∀ a, Fintype (β a)] :
    DecidablePred (· ∈ (sigmaCongrRightHom β).range) := fun _ => inferInstance

@[simp]
theorem sigmaCongrRightHom.card_range {α : Type*} {β : α → Type*}
    [Fintype (sigmaCongrRightHom β).range] [Fintype (∀ a, Perm (β a))] :
    Fintype.card (sigmaCongrRightHom β).range = Fintype.card (∀ a, Perm (β a)) :=
  Fintype.card_eq.mpr ⟨(ofInjective (sigmaCongrRightHom β) sigmaCongrRightHom_injective).symm⟩

instance subtypeCongrHom.decidableMemRange {α : Type*} (p : α → Prop) [DecidablePred p]
    [Fintype (Perm { a // p a } × Perm { a // ¬p a })] [DecidableEq (Perm α)] :
    DecidablePred (· ∈ (subtypeCongrHom p).range) := fun _ => inferInstance

@[simp]
theorem subtypeCongrHom.card_range {α : Type*} (p : α → Prop) [DecidablePred p]
    [Fintype (subtypeCongrHom p).range] [Fintype (Perm { a // p a } × Perm { a // ¬p a })] :
    Fintype.card (subtypeCongrHom p).range =
      Fintype.card (Perm { a // p a } × Perm { a // ¬p a }) :=
  Fintype.card_eq.mpr ⟨(ofInjective (subtypeCongrHom p) (subtypeCongrHom_injective p)).symm⟩

noncomputable def subgroupOfMulAction (G H : Type*) [Group G] [MulAction G H] [FaithfulSMul G H] :
    G ≃* (MulAction.toPermHom G H).range :=
  MulEquiv.ofLeftInverse' _ (Classical.choose_spec MulAction.toPerm_injective.hasLeftInverse)

end Perm

end Equiv
