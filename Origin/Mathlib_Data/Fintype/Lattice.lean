/-
Extracted from Data/Fintype/Lattice.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas relating fintypes and order/lattice structure.
-/

open Function

open Nat

universe u v

variable {ι α β : Type*}

namespace Finset

variable [Fintype α] {s : Finset α}

theorem sup_univ_eq_iSup [CompleteLattice β] (f : α → β) : Finset.univ.sup f = iSup f :=
  (sup_eq_iSup _ f).trans <| congr_arg _ <| funext fun _ => iSup_pos (mem_univ _)

theorem inf_univ_eq_iInf [CompleteLattice β] (f : α → β) : Finset.univ.inf f = iInf f :=
  @sup_univ_eq_iSup _ βᵒᵈ _ _ (f : α → βᵒᵈ)
