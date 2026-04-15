/-
Extracted from NumberTheory/NumberField/EquivReindex.lean
Genuine: 4 | Conflates: 0 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!

# Reindexed basis
This file introduces an equivalence between the set of embeddings of `K` into `ℂ` and the
index set of the chosen basis of the ring of integers of `K`.

## Tags

house, number field, algebraic number
-/

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

noncomputable section

open Module.Free Module canonicalEmbedding Matrix Finset

abbrev equivReindex : (K →+* ℂ) ≃ (ChooseBasisIndex ℤ (𝓞 K)) :=
    Fintype.equivOfCardEq <|
  by rw [Embeddings.card, ← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]

abbrev basisMatrix : Matrix (K →+* ℂ) (K →+* ℂ) ℂ :=
  (Matrix.of fun i ↦ latticeBasis K (equivReindex K i))

-- DISSOLVED: det_of_basisMatrix_non_zero

instance [DecidableEq (K →+* ℂ)] : Invertible (basisMatrix K) := invertibleOfIsUnitDet _
    (Ne.isUnit (det_of_basisMatrix_non_zero K))

variable {K}

theorem canonicalEmbedding_eq_basisMatrix_mulVec (α : K) :
    canonicalEmbedding K α = (basisMatrix K).transpose.mulVec
      (fun i ↦ (((integralBasis K).reindex (equivReindex K).symm).repr α i : ℂ)) := by
  ext i
  rw [← (latticeBasis K).sum_repr (canonicalEmbedding K α), ← Equiv.sum_comp (equivReindex K)]
  simp only [canonicalEmbedding.integralBasis_repr_apply, mulVec, dotProduct,
    transpose_apply, of_apply, Fintype.sum_apply, mul_comm, Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Pi.smul_apply, smul_eq_mul]

theorem inverse_basisMatrix_mulVec_eq_repr [DecidableEq (K →+* ℂ)] (α : 𝓞 K) :
    ∀ i, ((basisMatrix K).transpose)⁻¹.mulVec (fun j =>
      canonicalEmbedding K (algebraMap (𝓞 K) K α) j) i =
      ((integralBasis K).reindex (equivReindex K).symm).repr α i := fun i => by
  rw [inv_mulVec_eq_vec (canonicalEmbedding_eq_basisMatrix_mulVec ((algebraMap (𝓞 K) K) α))]

end

end NumberField
