/-
Extracted from GroupTheory/FreeGroup/GeneratorEquiv.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isomorphisms between free groups imply equivalences of their generators

-/

noncomputable section

variable {α β G H : Type*}

open IsFreeGroup Module

noncomputable def FreeAbelianGroup.basis (α : Type*) : Basis α ℤ (FreeAbelianGroup α) :=
  ⟨(FreeAbelianGroup.equivFinsupp α).toIntLinearEquiv⟩

def Equiv.ofFreeAbelianGroupLinearEquiv (e : FreeAbelianGroup α ≃ₗ[ℤ] FreeAbelianGroup β) : α ≃ β :=
  let t : Basis α ℤ (FreeAbelianGroup β) := (FreeAbelianGroup.basis α).map e
  t.indexEquiv <| FreeAbelianGroup.basis _

def Equiv.ofFreeAbelianGroupEquiv (e : FreeAbelianGroup α ≃+ FreeAbelianGroup β) : α ≃ β :=
  .ofFreeAbelianGroupLinearEquiv e.toIntLinearEquiv

def Equiv.ofFreeGroupEquiv (e : FreeGroup α ≃* FreeGroup β) : α ≃ β :=
  .ofFreeAbelianGroupEquiv (MulEquiv.toAdditive e.abelianizationCongr)

def Equiv.ofIsFreeGroupEquiv [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup H] (e : G ≃* H) :
    Generators G ≃ Generators H :=
  .ofFreeGroupEquiv <| (toFreeGroup G).symm.trans <| e.trans <| toFreeGroup H
