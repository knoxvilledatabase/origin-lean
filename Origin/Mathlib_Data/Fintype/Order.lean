/-
Extracted from Data/Fintype/Order.lean
Genuine: 17 of 21 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Order structures on finite types

This file provides order instances on fintypes.

## Computable instances

On a `Fintype`, we can construct
* an `OrderBot` from `SemilatticeInf`.
* an `OrderTop` from `SemilatticeSup`.
* a `BoundedOrder` from `Lattice`.

Those are marked as `def` to avoid defeqness issues.

## Completion instances

Those instances are noncomputable because the definitions of `sSup` and `sInf` use `Set.toFinset`
and set membership is undecidable in general.

On a `Fintype`, we can promote:
* a `Lattice` to a `CompleteLattice`.
* a `DistribLattice` to a `CompleteDistribLattice`.
* a `LinearOrder` to a `CompleteLinearOrder`.
* a `BooleanAlgebra` to a `CompleteAtomicBooleanAlgebra`.

Those are marked as `def` to avoid typeclass loops.

## Concrete instances

We provide a few instances for concrete types:
* `Fin.completeLinearOrder`
* `Bool.completeLinearOrder`
* `Bool.completeBooleanAlgebra`
-/

open Finset

namespace Fintype

variable {ι α : Type*} [Fintype ι] [Fintype α]

section Nonempty

variable (α) [Nonempty α]

abbrev toOrderBot [SemilatticeInf α] : OrderBot α where
  bot := univ.inf' univ_nonempty id
  bot_le a := inf'_le _ <| mem_univ a

abbrev toOrderTop [SemilatticeSup α] : OrderTop α where
  top := univ.sup' univ_nonempty id
  le_top a := le_sup' id <| mem_univ a

abbrev toBoundedOrder [Lattice α] : BoundedOrder α :=
  { toOrderBot α, toOrderTop α with }

end Nonempty

section BoundedOrder

variable (α)

open scoped Classical in

noncomputable abbrev toCompleteLattice [Lattice α] [BoundedOrder α] : CompleteLattice α where
  __ := ‹Lattice α›
  __ := ‹BoundedOrder α›
  sSup := fun s => s.toFinset.sup id
  sInf := fun s => s.toFinset.inf id
  isLUB_sSup s := Set.coe_toFinset s ▸ Finset.isLUB_sup_id
  isGLB_sInf s := Set.coe_toFinset s ▸ Finset.isGLB_inf_id

noncomputable abbrev toCompleteDistribLatticeMinimalAxioms [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice.MinimalAxioms α where
  __ := toCompleteLattice α
  iInf_sup_le_sup_sInf := fun a s => by
    convert (Finset.inf_sup_distrib_left s.toFinset id a).ge using 1
    rw [Finset.inf_eq_iInf]
    simp_rw [Set.mem_toFinset]
    rfl
  inf_sSup_le_iSup_inf := fun a s => by
    convert (Finset.sup_inf_distrib_left s.toFinset id a).le using 1
    rw [Finset.sup_eq_iSup]
    simp_rw [Set.mem_toFinset]
    rfl

noncomputable abbrev toCompleteDistribLattice [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice α := .ofMinimalAxioms (toCompleteDistribLatticeMinimalAxioms _)

noncomputable abbrev toCompleteLinearOrder
    [LinearOrder α] [BoundedOrder α] : CompleteLinearOrder α :=
  { toCompleteLattice α, ‹LinearOrder α›, LinearOrder.toBiheytingAlgebra _ with }

noncomputable abbrev toCompleteBooleanAlgebra [BooleanAlgebra α] : CompleteBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := Fintype.toCompleteDistribLattice α

noncomputable abbrev toCompleteAtomicBooleanAlgebra [BooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra α :=
  (toCompleteBooleanAlgebra α).toCompleteAtomicBooleanAlgebra

end BoundedOrder

section Nonempty

variable (α) [Nonempty α]

noncomputable abbrev toCompleteLatticeOfNonempty [Lattice α] : CompleteLattice α :=
  @toCompleteLattice _ _ _ <| toBoundedOrder α

noncomputable abbrev toCompleteLinearOrderOfNonempty [LinearOrder α] : CompleteLinearOrder α :=
  @toCompleteLinearOrder _ _ _ <| toBoundedOrder α

end Nonempty

end Fintype

/-! ### Concrete instances -/

-- INSTANCE (free from Core): Fin.completeLinearOrder

-- INSTANCE (free from Core): Bool.completeBooleanAlgebra

-- INSTANCE (free from Core): Bool.completeLinearOrder

-- INSTANCE (free from Core): Bool.completeAtomicBooleanAlgebra

/-! ### Directed Orders -/

section DirectedOrders

variable {α : Type*} {r : α → α → Prop} [IsTrans α r] {β γ : Type*} [Nonempty γ] {f : γ → α}
  [Finite β]

theorem Directed.finite_set_le (D : Directed r f) {s : Set γ} (hs : s.Finite) :
    ∃ z, ∀ i ∈ s, r (f i) (f z) := by
  convert D.finset_le hs.toFinset using 3; rw [Set.Finite.mem_toFinset]

theorem Directed.finite_le (D : Directed r f) (g : β → γ) : ∃ z, ∀ i, r (f (g i)) (f z) := by
  classical
    obtain ⟨z, hz⟩ := D.finite_set_le (Set.finite_range g)
    exact ⟨z, fun i => hz (g i) ⟨i, rfl⟩⟩

variable [Nonempty α] [Preorder α]

theorem Finite.exists_le [IsDirectedOrder α] (f : β → α) : ∃ M, ∀ i, f i ≤ M :=
  directed_id.finite_le _

theorem Finite.exists_ge [IsCodirectedOrder α] (f : β → α) : ∃ M, ∀ i, M ≤ f i :=
  directed_id.finite_le (r := (· ≥ ·)) _

theorem Set.Finite.exists_le [IsDirectedOrder α] {s : Set α} (hs : s.Finite) :
    ∃ M, ∀ i ∈ s, i ≤ M :=
  directed_id.finite_set_le hs

theorem Set.Finite.exists_ge [IsCodirectedOrder α] {s : Set α} (hs : s.Finite) :
    ∃ M, ∀ i ∈ s, M ≤ i :=
  directed_id.finite_set_le (r := (· ≥ ·)) hs
