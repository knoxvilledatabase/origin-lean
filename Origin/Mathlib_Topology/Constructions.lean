/-
Extracted from Topology/Constructions.lean
Genuine: 23 of 55 | Dissolved: 0 | Infrastructure: 32
-/
import Origin.Core

/-!
# Constructions of new topological spaces from old ones

This file constructs pi types, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, subspace, quotient space

-/

noncomputable section

open Topology TopologicalSpace Set Filter Function

open scoped Set.Notation

universe u v u' v'

variable {X : Type u} {Y : Type v} {Z W ε ζ : Type*}

section Constructions

-- INSTANCE (free from Core): {r

-- INSTANCE (free from Core): instTopologicalSpaceQuotient

-- INSTANCE (free from Core): instTopologicalSpaceSigma

-- INSTANCE (free from Core): Pi.topologicalSpace

-- INSTANCE (free from Core): ULift.topologicalSpace

/-!
### `Additive`, `Multiplicative`

The topology on those type synonyms is inherited without change.
-/

variable [TopologicalSpace X]

open Additive Multiplicative

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [DiscreteTopology

-- INSTANCE (free from Core): [DiscreteTopology

-- INSTANCE (free from Core): [CompactSpace

-- INSTANCE (free from Core): [CompactSpace

-- INSTANCE (free from Core): [NoncompactSpace

-- INSTANCE (free from Core): [NoncompactSpace

-- INSTANCE (free from Core): [WeaklyLocallyCompactSpace

-- INSTANCE (free from Core): [WeaklyLocallyCompactSpace

-- INSTANCE (free from Core): [LocallyCompactSpace

-- INSTANCE (free from Core): [LocallyCompactSpace

theorem continuous_ofMul : Continuous (ofMul : X → Additive X) := continuous_id

theorem continuous_toMul : Continuous (toMul : Additive X → X) := continuous_id

theorem continuous_ofAdd : Continuous (ofAdd : X → Multiplicative X) := continuous_id

theorem continuous_toAdd : Continuous (toAdd : Multiplicative X → X) := continuous_id

theorem isOpenMap_ofMul : IsOpenMap (ofMul : X → Additive X) := IsOpenMap.id

theorem isOpenMap_toMul : IsOpenMap (toMul : Additive X → X) := IsOpenMap.id

theorem isOpenMap_ofAdd : IsOpenMap (ofAdd : X → Multiplicative X) := IsOpenMap.id

theorem isOpenMap_toAdd : IsOpenMap (toAdd : Multiplicative X → X) := IsOpenMap.id

theorem isClosedMap_ofMul : IsClosedMap (ofMul : X → Additive X) := IsClosedMap.id

theorem isClosedMap_toMul : IsClosedMap (toMul : Additive X → X) := IsClosedMap.id

theorem isClosedMap_ofAdd : IsClosedMap (ofAdd : X → Multiplicative X) := IsClosedMap.id

theorem isClosedMap_toAdd : IsClosedMap (toAdd : Multiplicative X → X) := IsClosedMap.id

end

/-!
### Order dual

The topology on this type synonym is inherited without change.
-/

variable [TopologicalSpace X]

open OrderDual

-- INSTANCE (free from Core): OrderDual.instTopologicalSpace

-- INSTANCE (free from Core): OrderDual.instDiscreteTopology

theorem continuous_toDual : Continuous (toDual : X → Xᵒᵈ) := continuous_id

theorem continuous_ofDual : Continuous (ofDual : Xᵒᵈ → X) := continuous_id

theorem isOpenMap_toDual : IsOpenMap (toDual : X → Xᵒᵈ) := IsOpenMap.id

theorem isOpenMap_ofDual : IsOpenMap (ofDual : Xᵒᵈ → X) := IsOpenMap.id

theorem isClosedMap_toDual : IsClosedMap (toDual : X → Xᵒᵈ) := IsClosedMap.id

theorem isClosedMap_ofDual : IsClosedMap (ofDual : Xᵒᵈ → X) := IsClosedMap.id

variable [Preorder X] {x : X}

-- INSTANCE (free from Core): OrderDual.instNeBotNhdsWithinIoi

-- INSTANCE (free from Core): OrderDual.instNeBotNhdsWithinIio

end

theorem Quotient.preimage_mem_nhds [TopologicalSpace X] [s : Setoid X] {V : Set <| Quotient s}
    {x : X} (hs : V ∈ 𝓝 (Quotient.mk' x)) : Quotient.mk' ⁻¹' V ∈ 𝓝 x :=
  preimage_nhds_coinduced hs

theorem Dense.quotient [Setoid X] [TopologicalSpace X] {s : Set X} (H : Dense s) :
    Dense (Quotient.mk' '' s) :=
  Quotient.mk''_surjective.denseRange.dense_image continuous_coinduced_rng H

theorem DenseRange.quotient [Setoid X] [TopologicalSpace X] {f : Y → X} (hf : DenseRange f) :
    DenseRange (Quotient.mk' ∘ f) :=
  Quotient.mk''_surjective.denseRange.comp hf continuous_coinduced_rng

theorem continuous_map_of_le {α : Type*} [TopologicalSpace α]
    {s t : Setoid α} (h : s ≤ t) : Continuous (Setoid.map_of_le h) :=
  continuous_coinduced_rng

theorem continuous_map_sInf {α : Type*} [TopologicalSpace α]
    {S : Set (Setoid α)} {s : Setoid α} (h : s ∈ S) : Continuous (Setoid.map_sInf h) :=
  continuous_coinduced_rng

-- INSTANCE (free from Core): {p

-- INSTANCE (free from Core): Sum.discreteTopology

-- INSTANCE (free from Core): Sigma.discreteTopology

-- INSTANCE (free from Core): Prod.indiscreteTopology

-- INSTANCE (free from Core): Pi.indiscreteTopology
