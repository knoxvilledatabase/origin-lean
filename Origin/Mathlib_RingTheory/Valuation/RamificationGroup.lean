/-
Extracted from RingTheory/Valuation/RamificationGroup.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Ramification groups

The decomposition subgroup and inertia subgroups.

TODO: Define higher ramification groups in lower numbering
-/

namespace ValuationSubring

open scoped Pointwise

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

abbrev decompositionSubgroup (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  MulAction.stabilizer (L ≃ₐ[K] L) A

def subMulAction (A : ValuationSubring L) : SubMulAction (A.decompositionSubgroup K) L where
  carrier := A
  smul_mem' g _ h := Set.mem_of_mem_of_subset (Set.smul_mem_smul_set h) g.prop.le

-- INSTANCE (free from Core): decompositionSubgroupMulSemiringAction

noncomputable def inertiaSubgroup (A : ValuationSubring L) : Subgroup (A.decompositionSubgroup K) :=
  MonoidHom.ker <|
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

end ValuationSubring
