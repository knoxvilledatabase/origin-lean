/-
Extracted from LinearAlgebra/Eigenspace/Charpoly.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Eigenvalues are the roots of the characteristic polynomial.

## Tags

eigenvalue, characteristic polynomial
-/

namespace Module

namespace End

open LinearMap

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

lemma hasEigenvalue_iff_isRoot_charpoly (f : End R M) (μ : R) :
    f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ := by
  rw [hasEigenvalue_iff, eigenspace_def, ← det_eq_zero_iff_ker_ne_bot, det_eq_sign_charpoly_coeff]
  simp [Polynomial.coeff_zero_eq_eval_zero, charpoly_sub_smul]

lemma mem_spectrum_iff_isRoot_charpoly (f : End K V) (μ : K) :
    μ ∈ spectrum K f ↔ f.charpoly.IsRoot μ := by
  rw [← hasEigenvalue_iff_mem_spectrum, hasEigenvalue_iff_isRoot_charpoly]

lemma det_eq_prod_roots_charpoly_of_splits {f : End K V} (h : f.charpoly.Splits) :
    f.det = f.charpoly.roots.prod := by
  rw [← det_toMatrix (Module.Free.chooseBasis K V),
    Matrix.det_eq_prod_roots_charpoly_of_splits (by simpa using h), charpoly_toMatrix]

lemma trace_eq_sum_roots_charpoly_of_splits {f : End K V} (h : f.charpoly.Splits) :
    f.trace K V = f.charpoly.roots.sum := by
  let b := Module.Free.chooseBasis K V
  rw [trace_eq_matrix_trace K (Module.Free.chooseBasis K V),
    Matrix.trace_eq_sum_roots_charpoly_of_splits (by simpa using h), charpoly_toMatrix]

end End

end Module
