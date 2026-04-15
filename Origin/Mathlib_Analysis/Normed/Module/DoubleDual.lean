/-
Extracted from Analysis/Normed/Module/DoubleDual.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The double dual of a normed space

In this file we define the inclusion of a normed space into its double strong dual,
prove that it is an isometry (for `𝕜 = ℝ` or `𝕜 = ℂ`), and use the corresponding weak-topology
embedding together with Banach–Alaoglu to transfer compactness from the weak-star bidual back to
the weak topology.

## Main definitions

* `NormedSpace.inclusionInDoubleDual` is the inclusion of a normed space in its double
  `StrongDual`, considered as a bounded linear map.
* `NormedSpace.inclusionInDoubleDualLi` is the same map as a linear isometry (for `𝕜 = ℝ` or
  `𝕜 = ℂ`).
* `NormedSpace.inclusionInDoubleDualWeak` is the map from the weak space into the weak-star bidual,
  as a continuous linear map.
* `NormedSpace.isEmbedding_inclusionInDoubleDualWeak` shows that `inclusionInDoubleDualWeak` is
  a topological embedding.
* `NormedSpace.isCompact_closure_of_isBounded` transfers compactness from the weak-star topology
  on the bidual back to the weak topology on `X`.

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

double dual, inclusion, isometry, embedding, weak-star topology
-/

noncomputable section

open Topology Bornology WeakDual

universe u v

namespace NormedSpace

section inclusionInDoubleDual

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

def inclusionInDoubleDual : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜
