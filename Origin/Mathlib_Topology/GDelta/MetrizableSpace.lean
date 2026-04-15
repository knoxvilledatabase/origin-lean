/-
Extracted from Topology/GDelta/MetrizableSpace.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# `Gδ` sets and metrizable spaces

## Main results
We prove that metrizable spaces are T6.
We prove that the continuity set of a function from a topological space to a metrizable space is a
Gδ set.

-/

variable {X : Type*} [TopologicalSpace X]

open TopologicalSpace Set

section Metrizable

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end Metrizable

section ContinuousAt

variable {Y : Type*} [TopologicalSpace Y]

theorem IsGδ.setOf_continuousAt [PseudoMetrizableSpace Y] (f : X → Y) :
    IsGδ { x | ContinuousAt f x } := by
  let := pseudoMetrizableSpaceUniformity Y
  have := pseudoMetrizableSpaceUniformity_countably_generated Y
  obtain ⟨U, _, hU⟩ := (@uniformity_hasBasis_open_symmetric Y _).exists_antitone_subbasis
  simp only [Uniform.continuousAt_iff_prod, nhds_prod_eq]
  simp only [(nhds_basis_opens _).prod_self.tendsto_iff hU.toHasBasis,
    forall_prop_of_true, setOf_forall]
  refine .iInter fun k ↦ IsOpen.isGδ <| isOpen_iff_mem_nhds.2 fun x ↦ ?_
  rintro ⟨s, ⟨hsx, hso⟩, hsU⟩
  filter_upwards [IsOpen.mem_nhds hso hsx] with _ hy using ⟨s, ⟨hy, hso⟩, hsU⟩

end ContinuousAt
