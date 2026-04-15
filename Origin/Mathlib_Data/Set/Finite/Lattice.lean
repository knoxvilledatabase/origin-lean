/-
Extracted from Data/Set/Finite/Lattice.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Finiteness of unions and intersections

## Implementation notes

Each result in this file should come in three forms: a `Fintype` instance, a `Finite` instance
and a `Set.Finite` constructor.

## Tags

finite sets
-/

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

-- INSTANCE (free from Core): fintypeiUnion

-- INSTANCE (free from Core): fintypesUnion

lemma toFinset_iUnion [Fintype β] [DecidableEq α] (f : β → Set α)
    [∀ w, Fintype (f w)] :
    Set.toFinset (⋃ (x : β), f x) =
    Finset.biUnion (Finset.univ : Finset β) (fun x => (f x).toFinset) := by
  ext v
  simp only [mem_toFinset, mem_iUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
