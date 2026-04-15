/-
Extracted from Analysis/InnerProductSpace/CanonicalTensor.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Canonical tensors in real inner product spaces

Given an `InnerProductSpace ℝ E`, this file defines two canonical tensors.

* `InnerProductSpace.canonicalContravariantTensor E : E ⊗[ℝ] E →ₗ[ℝ] ℝ`. This is the element
  corresponding to the inner product.

* If `E` is finite-dimensional, then `E ⊗[ℝ] E` is canonically isomorphic to its dual. Accordingly,
  there exists an element `InnerProductSpace.canonicalCovariantTensor E : E ⊗[ℝ] E` that
  corresponds to `InnerProductSpace.canonicalContravariantTensor E` under this identification.

The theorem `canonicalCovariantTensor_eq_sum` shows that
`InnerProductSpace.canonicalCovariantTensor E` can be computed from any orthonormal basis `v` as
`∑ i, (v i) ⊗ₜ[ℝ] (v i)`.
-/

open InnerProductSpace TensorProduct

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def InnerProductSpace.canonicalContravariantTensor :
    E ⊗[ℝ] E →ₗ[ℝ] ℝ := lift (innerₗ E)

noncomputable def InnerProductSpace.canonicalCovariantTensor [FiniteDimensional ℝ E] :
    E ⊗[ℝ] E := ∑ i, ((stdOrthonormalBasis ℝ E) i) ⊗ₜ[ℝ] ((stdOrthonormalBasis ℝ E) i)

theorem InnerProductSpace.canonicalCovariantTensor_eq_sum [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) :
    InnerProductSpace.canonicalCovariantTensor E = ∑ i, (v i) ⊗ₜ[ℝ] (v i) := by
  let w := stdOrthonormalBasis ℝ E
  calc ∑ m, w m ⊗ₜ[ℝ] w m
  _ = ∑ m, ∑ n, ⟪w m, w n⟫_ℝ • w m ⊗ₜ[ℝ] w n := by
    congr 1 with m
    rw [Fintype.sum_eq_single m _, orthonormal_iff_ite.1 w.orthonormal]
    · simp only [↓reduceIte, one_smul]
    simp only [orthonormal_iff_ite.1 w.orthonormal, ite_smul, one_smul, zero_smul,
      ite_eq_right_iff]
    tauto
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_ℝ * ⟪v i, w n⟫_ℝ) • w m ⊗ₜ[ℝ] w n := by
    simp_rw [OrthonormalBasis.sum_inner_mul_inner v]
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_ℝ * ⟪w n, v i⟫_ℝ) • w m ⊗ₜ[ℝ] w n := by
    simp only [real_inner_comm (w _)]
  _ = ∑ i, (∑ m, ⟪w m, v i⟫_ℝ • w m) ⊗ₜ[ℝ] ∑ n, ⟪w n, v i⟫_ℝ • w n := by
    simp only [sum_tmul, tmul_sum, smul_tmul_smul, Finset.sum_comm (γ := ι), Finset.sum_smul]
    rw [Finset.sum_comm]
  _ = ∑ i, v i ⊗ₜ[ℝ] v i := by
    simp only [w.sum_repr' (v _)]
