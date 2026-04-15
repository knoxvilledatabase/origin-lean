/-
Extracted from Combinatorics/SimpleGraph/Ends/Properties.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Properties of the ends of graphs

This file is meant to contain results about the ends of (locally finite connected) graphs.

-/

variable {V : Type} (G : SimpleGraph V)

namespace SimpleGraph

-- INSTANCE (free from Core): [Finite

lemma end_componentCompl_infinite (e : G.end) (K : (Finset V)ᵒᵖ) :
    ((e : (j : (Finset V)ᵒᵖ) → G.componentComplFunctor.obj j) K).supp.Infinite := by
  refine (e.val K).infinite_iff_in_all_ranges.mpr (fun L h => ?_)
  change Opposite.unop K ⊆ Opposite.unop (Opposite.op L) at h
  exact ⟨e.val (Opposite.op L), (e.prop (CategoryTheory.opHomOfLE h))⟩

-- INSTANCE (free from Core): componentComplFunctor_nonempty_of_infinite

-- INSTANCE (free from Core): componentComplFunctor_finite

lemma nonempty_ends_of_infinite [LocallyFinite G] [Fact G.Preconnected] [Infinite V] :
    G.end.Nonempty := by
  classical
  apply nonempty_sections_of_finite_inverse_system G.componentComplFunctor

end SimpleGraph
