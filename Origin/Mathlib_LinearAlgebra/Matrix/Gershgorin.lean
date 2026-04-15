/-
Extracted from LinearAlgebra/Matrix/Gershgorin.lean
Genuine: 1 of 3 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# Gershgorin's circle theorem

This file gives the proof of Gershgorin's circle theorem `eigenvalue_mem_ball` on the eigenvalues
of matrices and some applications.

## Reference

* https://en.wikipedia.org/wiki/Gershgorin_circle_theorem
-/

variable {K n : Type*} [NormedField K] [Fintype n] [DecidableEq n] {A : Matrix n n K}

theorem eigenvalue_mem_ball {μ : K} (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
    ∃ k, μ ∈ Metric.closedBall (A k k) (∑ j ∈ Finset.univ.erase k, ‖A k j‖) := by
  cases isEmpty_or_nonempty n
  · exfalso
    exact hμ Submodule.eq_bot_of_subsingleton
  · obtain ⟨v, h_eg, h_nz⟩ := hμ.exists_hasEigenvector
    obtain ⟨i, -, h_i⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ‖v i‖)
    have h_nz : v i ≠ 0 := by
      contrapose! h_nz
      ext j
      rw [Pi.zero_apply, ← norm_le_zero_iff]
      refine (h_i ▸ Finset.le_sup' (fun i => ‖v i‖) (Finset.mem_univ j)).trans ?_
      exact norm_le_zero_iff.mpr h_nz
    have h_le : ∀ j, ‖v j * (v i)⁻¹‖ ≤ 1 := fun j => by
      rw [norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.mpr h_nz), one_mul]
      exact h_i ▸ Finset.le_sup' (fun i => ‖v i‖) (Finset.mem_univ j)
    simp_rw [mem_closedBall_iff_norm']
    refine ⟨i, ?_⟩
    calc
      _ = ‖(A i i * v i - μ * v i) * (v i)⁻¹‖ := by congr; field_simp [h_nz]; ring
      _ = ‖(A i i * v i - ∑ j, A i j * v j) * (v i)⁻¹‖ := by
                rw [show μ * v i = ∑ x : n, A i x * v x by
                  rw [← Matrix.dotProduct, ← Matrix.mulVec]
                  exact (congrFun (Module.End.mem_eigenspace_iff.mp h_eg) i).symm]
      _ = ‖(∑ j ∈ Finset.univ.erase i, A i j * v j) * (v i)⁻¹‖ := by
                rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), ← neg_sub, neg_mul, norm_neg]
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖ * ‖v j * (v i)⁻¹‖ := by
                rw [Finset.sum_mul]
                exact (norm_sum_le _ _).trans (le_of_eq (by simp_rw [mul_assoc, norm_mul]))
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖ :=
                (Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (norm_nonneg _) (h_le j))

-- DISSOLVED: det_ne_zero_of_sum_row_lt_diag

-- DISSOLVED: det_ne_zero_of_sum_col_lt_diag
