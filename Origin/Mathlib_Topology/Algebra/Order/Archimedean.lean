/-
Extracted from Topology/Algebra/Order/Archimedean.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topology on archimedean groups and fields

In this file we prove the following theorems:

- `Rat.denseRange_cast`: the coercion from `ℚ` to a linear ordered archimedean field has dense
  range;

- `AddSubgroup.dense_of_not_isolated_zero`, `AddSubgroup.dense_of_no_min`: two sufficient conditions
  for a subgroup of an archimedean linear ordered additive commutative group to be dense;

- `AddSubgroup.dense_or_cyclic`: an additive subgroup of an archimedean linear ordered additive
  commutative group `G` with order topology either is dense in `G` or is a cyclic subgroup.
-/

open Set

theorem Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [Archimedean 𝕜] : DenseRange ((↑) : ℚ → 𝕜) :=
  dense_of_exists_between fun _ _ h => Set.exists_range_iff.2 <| exists_rat_btwn h

namespace Subgroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
  [TopologicalSpace G] [OrderTopology G]
  [MulArchimedean G]
