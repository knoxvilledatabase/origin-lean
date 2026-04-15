/-
Extracted from Topology/Metrizable/Basic.lean
Genuine: 8 of 25 | Dissolved: 0 | Infrastructure: 17
-/
import Origin.Core

/-!
# Metrizable Spaces

In this file we define metrizable topological spaces, i.e., topological spaces for which there
exists a metric space structure that generates the same topology.
We define it without any reference to metric spaces in order to avoid importing the real numbers.
For the proof that metrizable spaces admit a compatible metric,
see `Mathlib/Topology/Metrizable/Uniformity.lean`.
-/

assert_not_exists AddMonoidWithOne

open Filter Set Topology Uniformity UniformSpace SetRel

namespace TopologicalSpace

variable {ι X Y : Type*} {A : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
  [∀ i, TopologicalSpace (A i)]

class PseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_countably_generated :
    ∃ u : UniformSpace X, u.toTopologicalSpace = t ∧ (uniformity X).IsCountablyGenerated

-- INSTANCE (free from Core): (priority

noncomputable abbrev pseudoMetrizableSpaceUniformity (X : Type*) [TopologicalSpace X]
    [h : PseudoMetrizableSpace X] : UniformSpace X :=
  h.exists_countably_generated.choose.replaceTopology
    h.exists_countably_generated.choose_spec.1.symm

example {X : Type*} [t : TopologicalSpace X] [PseudoMetrizableSpace X] :

    (pseudoMetrizableSpaceUniformity X).toTopologicalSpace = t := by

  with_reducible_and_instances rfl

-- INSTANCE (free from Core): pseudoMetrizableSpace_prod

theorem _root_.Topology.IsInducing.pseudoMetrizableSpace [PseudoMetrizableSpace Y] {f : X → Y}
    (hf : IsInducing f) : PseudoMetrizableSpace X :=
  let u : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated Y
  ⟨⟨u.comap f, u.toTopologicalSpace_comap.trans hf.eq_induced.symm,
    Filter.comap.isCountablyGenerated (uniformity Y) (Prod.map f f)⟩⟩

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): PseudoMetrizableSpace.subtype

-- INSTANCE (free from Core): pseudoMetrizableSpace_pi

-- INSTANCE (free from Core): PseudoMetrizableSpace.regularSpace

-- INSTANCE (free from Core): (priority

class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop extends
    PseudoMetrizableSpace X, T0Space X

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): metrizableSpace_prod

theorem _root_.Topology.IsEmbedding.metrizableSpace [MetrizableSpace Y] {f : X → Y}
    (hf : IsEmbedding f) : MetrizableSpace X where
  toPseudoMetrizableSpace := hf.toIsInducing.pseudoMetrizableSpace
  toT0Space := hf.t0Space

-- INSTANCE (free from Core): MetrizableSpace.subtype

-- INSTANCE (free from Core): metrizableSpace_pi

theorem IsSeparable.secondCountableTopology [PseudoMetrizableSpace X] {s : Set X}
    (hs : IsSeparable s) : SecondCountableTopology s :=
  let ⟨u, hu, hs⟩ := hs
  have := hu.to_subtype
  have : SeparableSpace (closure u) :=
    ⟨Set.range (u.inclusion subset_closure), Set.countable_range (u.inclusion subset_closure),
      Subtype.dense_iff.2 <| by rw [← Set.range_comp, Set.val_comp_inclusion, Subtype.range_coe]⟩
  let := pseudoMetrizableSpaceUniformity (closure u)
  have := pseudoMetrizableSpaceUniformity_countably_generated (closure u)
  have := secondCountable_of_separable (closure u)
  (Topology.IsEmbedding.inclusion hs).secondCountableTopology

-- INSTANCE (free from Core): (X

theorem IsSeparable.exists_countable_dense_subset [PseudoMetrizableSpace X]
    {s : Set X} (hs : IsSeparable s) : ∃ t, t ⊆ s ∧ t.Countable ∧ s ⊆ closure t := by
  let := pseudoMetrizableSpaceUniformity X
  have := pseudoMetrizableSpaceUniformity_countably_generated X
  apply subset_countable_closure_of_almost_dense_set
  intro U hU
  obtain ⟨t, htc, hst⟩ := hs
  refine ⟨t, htc, fun x hx => ?_⟩
  obtain ⟨y, hyx, hyt⟩ := mem_closure_iff_ball.1 (hst hx) (symmetrize_mem_uniformity hU)
  exact mem_biUnion hyt (ball_mono SetRel.symmetrize_subset_inv x hyx)

theorem IsSeparable.separableSpace [PseudoMetrizableSpace X] {s : Set X} (hs : IsSeparable s) :
    SeparableSpace s := by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, hst⟩
  lift t to Set s using hts
  refine ⟨⟨t, countable_of_injective_of_countable_image Subtype.coe_injective.injOn htc, ?_⟩⟩
  rwa [IsInducing.subtypeVal.dense_iff, Subtype.forall]

-- INSTANCE (free from Core): (priority

end TopologicalSpace
