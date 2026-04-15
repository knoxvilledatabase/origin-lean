/-
Extracted from Analysis/Matrix/Order.lean
Genuine: 13 of 14 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The partial order on matrices

This file constructs the partial order and star ordered instances on matrices on `𝕜`.
This allows us to use more general results from C⋆-algebras, like `CFC.sqrt`.

## Main results

* `Matrix.instPartialOrder`: the partial order on matrices given by `x ≤ y := (y - x).PosSemidef`.
* `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`: for a positive semi-definite matrix `A`,
  we have `x⋆ A x = 0` iff `A x = 0`.
* `Matrix.toMatrixInnerProductSpace`: the inner product on matrices induced by a
  positive semi-definite matrix `M`: `⟪x, y⟫ = (y * M * xᴴ).trace`.

## Implementation notes

Note that the partial order instance is scoped to `MatrixOrder`.
Please `open scoped MatrixOrder` to use this.
-/

variable {𝕜 n : Type*} [RCLike 𝕜]

open scoped ComplexOrder

open Matrix

namespace Matrix

section PartialOrder

abbrev instPreOrder : Preorder (Matrix n n 𝕜) where
  le A B := (B - A).PosSemidef
  le_refl A := sub_self A ▸ PosSemidef.zero
  le_trans A B C h₁ h₂ := sub_add_sub_cancel C B A ▸ h₂.add h₁

scoped[MatrixOrder] attribute [instance] Matrix.instPreOrder

open MatrixOrder

lemma nonneg_iff_posSemidef {A : Matrix n n 𝕜} : 0 ≤ A ↔ A.PosSemidef := by rw [le_iff, sub_zero]

protected alias ⟨LE.le.posSemidef, PosSemidef.nonneg⟩ := nonneg_iff_posSemidef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosSemidef.nonneg

private lemma le_antisymm_aux {A : Matrix n n 𝕜} (h₁ : A.PosSemidef) (h₂ : (-A).PosSemidef) :
    A = 0 := by
  classical
  ext i j
  have hdiag i : A i i = 0 :=
    le_antisymm (by simpa using h₂.diag_nonneg) (by simpa using h₁.diag_nonneg)
  have h1 := h₁.2 (.single i 1 + .single j (A j i))
  have h2 := h₂.2 (.single i 1 + .single j (A j i))
  simp [Finsupp.sum_add_index, mul_add, add_mul,
      -neg_add_rev, hdiag, ← h₁.1.apply j i, -RCLike.star_def] at *
  simpa using le_antisymm h2 h1

abbrev instPartialOrder : PartialOrder (Matrix n n 𝕜) where
  le_antisymm A B h₁ h₂ := by
    simpa [sub_eq_zero, eq_comm] using le_antisymm_aux h₁
     (by simpa only [← neg_sub B, le_iff] using h₂)

scoped[MatrixOrder] attribute [instance] Matrix.instPartialOrder

lemma instIsOrderedAddMonoid : IsOrderedAddMonoid (Matrix n n 𝕜) where
  add_le_add_left _ _ _ _ := by rwa [le_iff, add_sub_add_right_eq_sub]

scoped[MatrixOrder] attribute [instance] Matrix.instIsOrderedAddMonoid

variable [Fintype n]

lemma instNonnegSpectrumClass : NonnegSpectrumClass ℝ (Matrix n n 𝕜) where
  quasispectrum_nonneg_of_nonneg A hA := by
    classical
    simp only [quasispectrum_eq_spectrum_union_zero ℝ A, Set.union_singleton, Set.mem_insert_iff,
      forall_eq_or_imp, le_refl, true_and]
    intro x hx
    obtain ⟨i, rfl⟩ := Set.ext_iff.mp
      hA.posSemidef.1.spectrum_real_eq_range_eigenvalues x |>.mp hx
    exact hA.posSemidef.eigenvalues_nonneg _

scoped[MatrixOrder] attribute [instance] instNonnegSpectrumClass

lemma instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
  .of_nonneg_iff' add_le_add_right fun A ↦
    ⟨fun hA ↦ by
      classical
      obtain ⟨X, hX, -, rfl⟩ :=
        sub_zero A ▸ CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hA.isHermitian
          (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
      exact ⟨X, hX.star_eq.symm ▸ rfl⟩,
    fun ⟨A, hA⟩ => hA ▸ (posSemidef_conjTranspose_mul_self A).nonneg⟩

scoped[MatrixOrder] attribute [instance] instStarOrderedRing

end PartialOrder

open scoped MatrixOrder

variable [Fintype n]

namespace PosSemidef

section sqrtDeprecated

variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)

include hA

lemma inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ := by
  rw [eq_comm, CFC.sqrt_eq_iff _ _ hA.inv.nonneg (CFC.sqrt_nonneg A).posSemidef.inv.nonneg, ← sq,
    inv_pow', CFC.sq_sqrt A]

end sqrtDeprecated

theorem dotProduct_mulVec_zero_iff {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    star x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ dotProduct_zero _⟩
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp_rw [← Matrix.mulVec_mulVec, dotProduct_mulVec _ _ (B *ᵥ x), star_eq_conjTranspose,
    vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero] at h ⊢
  rw [h, mulVec_zero]

theorem toLinearMap₂'_zero_iff [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    Matrix.toLinearMap₂' 𝕜 A (star x) x = 0 ↔ A *ᵥ x = 0 := by
  simpa only [toLinearMap₂'_apply'] using hA.dotProduct_mulVec_zero_iff x

theorem det_sqrt [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    (CFC.sqrt A).det = RCLike.sqrt A.det := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A, hA.1.cfc_eq, RCLike.sqrt_of_nonneg hA.det_nonneg]
  simp only [IsHermitian.cfc, Real.coe_sqrt, Real.coe_toNNReal', det_map, det_diagonal,
    Function.comp_apply, hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod,
    RCLike.ofReal_re, Real.sqrt_prod _ fun _ _ ↦ hA.eigenvalues_nonneg _]
  grind

end PosSemidef

theorem IsHermitian.det_abs [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    det (CFC.abs A) = ‖det A‖ := by
  rw [CFC.abs_eq_cfc_norm A, hA.cfc_eq]
  simp [IsHermitian.cfc, -Unitary.conjStarAlgAut_apply, hA.det_eq_prod_eigenvalues]

theorem posSemidef_iff_isHermitian_and_spectrum_nonneg [DecidableEq n] {A : Matrix n n 𝕜} :
    A.PosSemidef ↔ A.IsHermitian ∧ spectrum 𝕜 A ⊆ {a : 𝕜 | 0 ≤ a} := by
  refine ⟨fun h => ⟨h.isHermitian, fun a => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · simp only [h.isHermitian.spectrum_eq_image_range, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, Set.mem_setOf_eq, forall_exists_index]
    rintro i rfl
    exact_mod_cast h.eigenvalues_nonneg _
  · rw [h1.posSemidef_iff_eigenvalues_nonneg]
    intro i
    simpa [h1.spectrum_eq_image_range] using @h2 (h1.eigenvalues i)
