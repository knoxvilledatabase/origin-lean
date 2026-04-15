/-
Extracted from NumberTheory/LocalField/Basic.lean
Genuine: 1 of 12 | Dissolved: 2 | Infrastructure: 9
-/
import Origin.Core

/-!

# Definition of (Non-archimedean) local fields

Given a topological field `K` equipped with an equivalence class of valuations (a `ValuativeRel`),
we say that it is a non-archimedean local field if the topology comes from the given valuation,
and it is locally compact and non-discrete.

-/

class IsNonarchimedeanLocalField
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] : Prop extends
  IsValuativeTopology K,
  LocallyCompactSpace K,
  ValuativeRel.IsNontrivial K

open ValuativeRel Valued.integer

open scoped WithZero

namespace IsNonarchimedeanLocalField

section TopologicalSpace

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local simp] zero_lt_iff

-- INSTANCE (free from Core): :

-- DISSOLVED: isCompact_closedBall

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (K

-- INSTANCE (free from Core): :

noncomputable

-- DISSOLVED: valueGroupWithZeroIsoInt

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

proof_wanted isAdicComplete : IsAdicComplete 𝓂[K] 𝒪[K]

end TopologicalSpace

section UniformSpace

variable (K : Type*) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end UniformSpace

end IsNonarchimedeanLocalField
