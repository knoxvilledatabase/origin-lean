/-
Extracted from Topology/Covering/AddCircle.lean
Genuine: 5 of 7 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Covering maps involving `AddCircle`

-/

namespace AddCircle

section AddCommGroup

open AddSubgroup

variable {𝕜 : Type*} [AddCommGroup 𝕜] (p : 𝕜) [TopologicalSpace 𝕜] [IsTopologicalAddGroup 𝕜]
  [DiscreteTopology (zmultiples p)]

theorem isAddQuotientCoveringMap_coe :
    IsAddQuotientCoveringMap ((↑) : 𝕜 → AddCircle p) (zmultiples p) :=
  isAddQuotientCoveringMap_of_comm _ DiscreteTopology.isDiscrete

theorem isCoveringMap_coe : IsCoveringMap ((↑) : 𝕜 → AddCircle p) :=
  (isAddQuotientCoveringMap_coe p).isCoveringMap

theorem isLocalHomeomorph_coe : IsLocalHomeomorph ((↑) : 𝕜 → AddCircle p) :=
  (isCoveringMap_coe p).isLocalHomeomorph

end AddCommGroup

section Field

open Topology

variable {𝕜 : Type*} [TopologicalSpace 𝕜] [Ring 𝕜] [IsTopologicalRing 𝕜]

variable (p : 𝕜) [T0Space (AddCircle p)]

theorem isAddQuotientCoveringMap_zsmul {n : ℤ} (hn : IsUnit (n : 𝕜)) :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _)
      (zsmulAddGroupHom (α := AddCircle p) n).ker := by
  refine hn.isQuotientMap_zsmul (QuotientAddGroup.mk' _) isQuotientMap_quotient_mk'
    |>.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom
    (f := zsmulAddGroupHom (α := AddCircle p) n)
    (Set.Finite.isDiscrete <| finite_torsion_of_isSMulRegular_int _ _ fun _ ↦ ?_)
  simp_rw [zsmul_eq_mul]
  apply hn.isSMulRegular 𝕜

theorem isAddQuotientCoveringMap_nsmul {n : ℕ} (hn : IsUnit (n : 𝕜)) :
    IsAddQuotientCoveringMap (n • · : AddCircle p → _)
      (nsmulAddMonoidHom (α := AddCircle p) n).ker := by
  convert isAddQuotientCoveringMap_zsmul p (n := n) (mod_cast hn)
  all_goals ext; simp

-- DISSOLVED: isAddQuotientCoveringMap_zsmul_of_ne_zero

-- DISSOLVED: isAddQuotientCoveringMap_nsmul_of_ne_zero

end Field

end AddCircle
