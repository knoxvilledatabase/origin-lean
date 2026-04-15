/-
Extracted from Topology/Separation/Connected.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Interaction of separation properties with connectedness properties
-/

variable {X : Type*} [TopologicalSpace X]

open Filter Set

open scoped Topology

-- INSTANCE (free from Core): (priority

theorem PreconnectedSpace.trivial_of_discrete [PreconnectedSpace X] [DiscreteTopology X] :
    Subsingleton X := by
  by_contra! ⟨x, y, hxy⟩
  rw [Ne, ← mem_singleton_iff, (isClopen_discrete _).eq_univ <| singleton_nonempty y] at hxy
  exact hxy (mem_univ x)

theorem IsPreconnected.infinite_of_nontrivial [T1Space X] {s : Set X} (h : IsPreconnected s)
    (hs : s.Nontrivial) : s.Infinite := by
  refine mt (fun hf => (subsingleton_coe s).mp ?_) (not_subsingleton_iff.mpr hs)
  haveI := @Finite.instDiscreteTopology s _ _ hf.to_subtype
  exact @PreconnectedSpace.trivial_of_discrete _ _ (Subtype.preconnectedSpace h) _

theorem PreconnectedSpace.infinite [PreconnectedSpace X] [Nontrivial X] [T1Space X] : Infinite X :=
  infinite_univ_iff.mp <| isPreconnected_univ.infinite_of_nontrivial nontrivial_univ

-- INSTANCE (free from Core): (priority
