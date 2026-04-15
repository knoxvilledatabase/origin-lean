/-
Extracted from Topology/MetricSpace/Pseudo/Constructions.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Products of pseudometric spaces and other constructions

This file constructs the supremum distance on binary products of pseudometric spaces and provides
instances for type synonyms.
-/

open Bornology Filter Metric Set Topology

open scoped NNReal

variable {α β : Type*} [PseudoMetricSpace α]

abbrev PseudoMetricSpace.induced {α β} (f : α → β) (m : PseudoMetricSpace β) :
    PseudoMetricSpace α where
  dist x y := dist (f x) (f y)
  dist_self _ := dist_self _
  dist_comm _ _ := dist_comm _ _
  dist_triangle _ _ _ := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist _ _ := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
  cobounded_sets := Set.ext fun s => mem_comap_iff_compl.trans <| by
    simp only [← isBounded_def, isBounded_iff, forall_mem_image, mem_setOf]
