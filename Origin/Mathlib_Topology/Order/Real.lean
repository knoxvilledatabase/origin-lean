/-
Extracted from Topology/Order/Real.lean
Genuine: 1 of 10 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# The reals are equipped with their order topology

This file contains results related to the order topology on (extended) (non-negative) real numbers.
We
- prove that `ℝ` and `ℝ≥0` are equipped with the order topology and bornology,
- endow `EReal` with the order topology (and prove some very basic lemmas),
- define the topology `ℝ≥0∞` (which is the order topology, *not* the `EMetricSpace` topology)
-/

assert_not_exists IsTopologicalRing UniformSpace

open Set

namespace EReal

/-!
### Topological structure on `EReal`

We endow `EReal` with the order topology.
Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

lemma denseRange_ratCast : DenseRange (fun r : ℚ ↦ ((r : ℝ) : EReal)) :=
  dense_of_exists_between fun _ _ h => exists_range_iff.2 <| exists_rat_btwn_of_lt h

end EReal

namespace ENNReal

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end ENNReal
