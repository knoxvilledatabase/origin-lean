/-
Extracted from Order/Atoms/Finite.lean
Genuine: 4 of 11 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Atoms, Coatoms, Simple Lattices, and Finiteness

This module contains some results on atoms and simple lattices in the finite context.

## Main results
* `Finite.to_isAtomic`, `Finite.to_isCoatomic`: Finite partial orders with bottom resp. top
  are atomic resp. coatomic.

-/

variable {α β : Type*}

namespace IsSimpleOrder

variable [LE α] [BoundedOrder α] [IsSimpleOrder α]

section DecidableEq

-- INSTANCE (free from Core): (priority

end DecidableEq

-- INSTANCE (free from Core): (priority

end IsSimpleOrder

namespace Fintype

namespace IsSimpleOrder

open scoped _root_.IsSimpleOrder

variable [LE α] [BoundedOrder α] [IsSimpleOrder α] [DecidableEq α]

theorem univ : (Finset.univ : Finset α) = {⊤, ⊥} := by
  ext
  simpa using (eq_bot_or_eq_top _).symm

theorem card : Fintype.card α = 2 :=
  (Fintype.ofEquiv_card _).trans Fintype.card_bool

end IsSimpleOrder

end Fintype

namespace Bool

-- INSTANCE (free from Core): :

end Bool

section Fintype

open Finset

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end Fintype

section LocallyFinite

variable [Preorder α] [LocallyFiniteOrder α]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end LocallyFinite

section IsStronglyAtomic

variable [PartialOrder α] {a : α}

theorem exists_covby_infinite_Ici_of_infinite_Ici [IsStronglyAtomic α]
    (ha : (Set.Ici a).Infinite) (hfin : {x | a ⋖ x}.Finite) :
    ∃ b, a ⋖ b ∧ (Set.Ici b).Infinite := by
  by_contra! h
  refine ((hfin.biUnion (t := Set.Ici) (by simpa using h)).subset (fun b hb ↦ ?_)).not_infinite
    (ha.diff (Set.finite_singleton a))
  obtain ⟨x, hax, hxb⟩ := ((show a ≤ b from hb.1).lt_of_ne (Ne.symm hb.2)).exists_covby_le
  exact Set.mem_biUnion hax hxb

theorem exists_covby_infinite_Iic_of_infinite_Iic [IsStronglyCoatomic α]
    (ha : (Set.Iic a).Infinite) (hfin : {x | x ⋖ a}.Finite) :
    ∃ b, b ⋖ a ∧ (Set.Iic b).Infinite := by
  simp_rw [← toDual_covBy_toDual_iff (α := α)] at hfin ⊢
  exact exists_covby_infinite_Ici_of_infinite_Ici (α := αᵒᵈ) ha hfin

end IsStronglyAtomic
