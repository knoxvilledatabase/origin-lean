/-
Extracted from Algebra/Order/Module/Field.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Ordered vector spaces
-/

open OrderDual

variable {𝕜 G : Type*}

section LinearOrderedSemifield

variable [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup G] [PartialOrder G]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end LinearOrderedSemifield

section Field

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [Module 𝕜 G] {a : 𝕜} {b₁ b₂ : G}

section PosSMulMono

variable [PosSMulMono 𝕜 G]

lemma inv_smul_le_iff_of_neg (h : a < 0) : a⁻¹ • b₁ ≤ b₂ ↔ a • b₂ ≤ b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]

lemma smul_inv_le_iff_of_neg (h : a < 0) : b₁ ≤ a⁻¹ • b₂ ↔ b₂ ≤ a • b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]

variable (G)
