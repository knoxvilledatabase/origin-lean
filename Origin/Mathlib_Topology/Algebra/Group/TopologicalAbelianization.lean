/-
Extracted from Topology/Algebra/Group/TopologicalAbelianization.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The topological abelianization of a group.

This file defines the topological abelianization of a topological group.

## Main definitions

* `TopologicalAbelianization`: defines the topological abelianization of a group `G` as the quotient
  of `G` by the topological closure of its commutator subgroup..

## Main results
- `instNormalCommutatorClosure` : the topological closure of the commutator of a topological group
  `G` is a normal subgroup.

## Tags
group, topological abelianization

-/

open scoped commutatorElement

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

-- INSTANCE (free from Core): instNormalCommutatorClosure

abbrev TopologicalAbelianization := G ⧸ Subgroup.topologicalClosure (commutator G)

local notation "G_ab" => TopologicalAbelianization

namespace TopologicalAbelianization

-- INSTANCE (free from Core): commGroup

end TopologicalAbelianization
