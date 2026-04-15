/-
Extracted from Analysis/CStarAlgebra/Matrix.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Analytic properties of the `star` operation on matrices

This transports the operator norm on `EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m` to
`Matrix m n 𝕜`. See the file `Mathlib/Analysis/Matrix.lean` for many other matrix norms.

## Main definitions

* `Matrix.instNormedRingL2Op`: the (necessarily unique) normed ring structure on `Matrix n n 𝕜`
  which ensure it is a `CStarRing` in `Matrix.instCStarRing`. This is a scoped instance in the
  namespace `Matrix.Norms.L2Operator` in order to avoid choosing a global norm for `Matrix`.

## Main statements

* `entry_norm_bound_of_unitary`: the entries of a unitary matrix are uniformly bound by `1`.

## Implementation details

We take care to ensure the topology and uniformity induced by `Matrix.instMetricSpaceL2Op`
coincide with the existing topology and uniformity on matrices.

-/

open WithLp

open scoped Matrix

variable {𝕜 m n l E : Type*}

section EntrywiseSupNorm

variable [RCLike 𝕜] [Fintype n] [DecidableEq n]

theorem entry_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (i j : n) : ‖U i j‖ ≤ 1 := by
  -- The norm squared of an entry is at most the L2 norm of its row.
  have norm_sum : ‖U i j‖ ^ 2 ≤ ∑ x, ‖U i x‖ ^ 2 := by
    apply Multiset.single_le_sum
    · intro x h_x
      rw [Multiset.mem_map] at h_x
      obtain ⟨a, h_a⟩ := h_x
      rw [← h_a.2]
      apply sq_nonneg
    · rw [Multiset.mem_map]
      use j
      simp only [Finset.mem_univ_val, and_self_iff]
  -- The L2 norm of a row is a diagonal entry of U * Uᴴ
  have diag_eq_norm_sum : (U * Uᴴ) i i = (∑ x : n, ‖U i x‖ ^ 2 : ℝ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply, RCLike.mul_conj]
    norm_cast
  -- The L2 norm of a row is a diagonal entry of U * Uᴴ, real part
  have re_diag_eq_norm_sum : RCLike.re ((U * Uᴴ) i i) = ∑ x : n, ‖U i x‖ ^ 2 := by
    rw [RCLike.ext_iff] at diag_eq_norm_sum
    rw [diag_eq_norm_sum.1]
    norm_cast
  -- Since U is unitary, the diagonal entries of U * Uᴴ are all 1
  have mul_eq_one : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hU
  have diag_eq_one : RCLike.re ((U * Uᴴ) i i) = 1 := by
    simp only [mul_eq_one, Matrix.one_apply_eq, RCLike.one_re]
  -- Putting it all together
  rw [← sq_le_one_iff₀ (norm_nonneg (U i j)), ← diag_eq_one, re_diag_eq_norm_sum]
  exact norm_sum

set_option backward.isDefEq.respectTransparency false in

open scoped Matrix.Norms.Elementwise in

theorem entrywise_sup_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    ‖U‖ ≤ 1 := by
  simp_rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intros
  exact entry_norm_bound_of_unitary hU _ _

end EntrywiseSupNorm

noncomputable section L2OpNorm

namespace Matrix

open LinearMap

variable [RCLike 𝕜]

variable [Fintype m] [Fintype n] [DecidableEq n] [Fintype l] [DecidableEq l]

def toEuclideanCLM :
    Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) :=
  toMatrixOrthonormal (EuclideanSpace.basisFun n 𝕜) |>.symm.trans <|
    { toContinuousLinearMap with
      map_mul' := fun _ _ ↦ rfl
      map_star' := adjoint_toContinuousLinearMap }
