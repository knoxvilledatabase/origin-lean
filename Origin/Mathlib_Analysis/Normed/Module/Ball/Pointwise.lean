/-
Extracted from Analysis/Normed/Module/Ball/Pointwise.lean
Genuine: 3 of 4 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Properties of pointwise scalar multiplication of sets in normed spaces.

We explore the relationships between scalar multiplication of sets in vector spaces, and the norm.
Notably, we express arbitrary balls as rescaling of other balls, and we show that the
multiplication of bounded sets remain bounded.
-/

open Metric Set

open Pointwise Topology

variable {𝕜 E : Type*}

section SMulZeroClass

variable [SeminormedAddCommGroup 𝕜] [SeminormedAddCommGroup E]

variable [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E]

theorem ediam_smul_le (c : 𝕜) (s : Set E) : ediam (c • s) ≤ ‖c‖₊ • ediam s :=
  (lipschitzWith_smul c).ediam_image_le s

end SMulZeroClass

section DivisionRing

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E]

variable [Module 𝕜 E] [NormSMulClass 𝕜 E]

theorem ediam_smul₀ (c : 𝕜) (s : Set E) : ediam (c • s) = ‖c‖₊ • ediam s := by
  refine le_antisymm (ediam_smul_le c s) ?_
  obtain rfl | hc := eq_or_ne c 0
  · obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    simp [zero_smul_set hs, ← Set.singleton_zero]
  · have := (lipschitzWith_smul c⁻¹).ediam_image_le (c • s)
    rwa [← smul_eq_mul, ← ENNReal.smul_def, Set.image_smul, inv_smul_smul₀ hc s, nnnorm_inv,
      le_inv_smul_iff_of_pos (nnnorm_pos.2 hc)] at this

theorem diam_smul₀ (c : 𝕜) (x : Set E) : diam (c • x) = ‖c‖ * diam x := by
  simp_rw [diam, ediam_smul₀, ENNReal.toReal_smul, NNReal.smul_def, coe_nnnorm, smul_eq_mul]

-- DISSOLVED: infEDist_smul₀
