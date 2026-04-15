/-
Extracted from Order/CompleteBooleanAlgebra.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Frames, completely distributive lattices and complete Boolean algebras

In this file we define and provide API for (co)frames, completely distributive lattices and
complete Boolean algebras.

We distinguish two different distributivity properties:
1. `inf_iSup_eq : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i` (finite `⊓` distributes over infinite `⨆`).
  This is required by `Frame`, `CompleteDistribLattice`, and `CompleteBooleanAlgebra`
  (`Coframe`, etc., require the dual property).
2. `iInf_iSup_eq : (⨅ i, ⨆ j, f i j) = ⨆ s, ⨅ i, f i (s i)`
  (infinite `⨅` distributes over infinite `⨆`).
  This stronger property is called "completely distributive",
  and is required by `CompletelyDistribLattice` and `CompleteAtomicBooleanAlgebra`.

## Typeclasses

* `Order.Frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `Order.Coframe`: Coframe: A complete lattice whose `⊔` distributes over `⨅`.
* `CompleteDistribLattice`: Complete distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `CompletelyDistribLattice`: Completely distributive lattices: A complete lattice whose
  `⨅` and `⨆` satisfy `iInf_iSup_eq`.
* `CompleteBooleanAlgebra`: Complete Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.
* `CompleteAtomicBooleanAlgebra`: Complete atomic Boolean algebra:
  A complete Boolean algebra which is additionally completely distributive.
  (This implies that it's (co)atom(ist)ic.)

A set of opens gives rise to a topological space precisely if it forms a frame. Such a frame is also
completely distributive, but not all frames are. `Filter` is a coframe but not a completely
distributive lattice.

## References

* [Wikipedia, *Complete Heyting algebra*](https://en.wikipedia.org/wiki/Complete_Heyting_algebra)
* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

open Function Set

universe u v w w'

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort w'}

class Order.Frame.MinimalAxioms (α : Type u) extends CompleteLattice α where
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b

class Order.Coframe.MinimalAxioms (α : Type u) extends CompleteLattice α where
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s

class Order.Frame (α : Type*) extends CompleteLattice α, HeytingAlgebra α where

theorem inf_sSup_eq {α : Type*} [Order.Frame α] {s : Set α} {a : α} :
    a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  gc_inf_himp.l_sSup
