/-
Extracted from Order/Interval/Set/OrdConnectedComponent.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Order connected components of a set

In this file we define `Set.ordConnectedComponent s x` to be the set of `y` such that
`Set.uIcc x y ⊆ s` and prove some basic facts about this definition. At the moment of writing,
this construction is used only to prove that any linear order with order topology is a T₅ space,
so we only add API needed for this lemma.
-/

open Interval Function OrderDual

namespace Set

variable {α : Type*} [LinearOrder α] {s t : Set α} {x y z : α}

def ordConnectedComponent (s : Set α) (x : α) : Set α :=
  { y | [[x, y]] ⊆ s }

theorem dual_ordConnectedComponent :
    ordConnectedComponent (ofDual ⁻¹' s) (toDual x) = ofDual ⁻¹' ordConnectedComponent s x :=
  ext <| (Surjective.forall toDual.surjective).2 fun x => by simp [mem_ordConnectedComponent]

theorem ordConnectedComponent_subset : ordConnectedComponent s x ⊆ s := fun _ hy =>
  hy right_mem_uIcc

theorem subset_ordConnectedComponent {t} [h : OrdConnected s] (hs : x ∈ s) (ht : s ⊆ t) :
    s ⊆ ordConnectedComponent t x := fun _ hy => (h.uIcc_subset hs hy).trans ht
