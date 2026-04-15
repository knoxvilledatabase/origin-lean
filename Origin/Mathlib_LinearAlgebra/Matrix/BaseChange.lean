/-
Extracted from LinearAlgebra/Matrix/BaseChange.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Matrices and base change

This file is a home for results about base change for matrices.

## Main results:
* `Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right`: if an invertible matrix over `L` takes
  values in subfield `K ⊆ L`, then so does its (right) inverse.
* `Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left`: if an invertible matrix over `L` takes
  values in subfield `K ⊆ L`, then so does its (left) inverse.

-/

namespace Matrix

variable {m n L : Type*} [Finite m] [Fintype n] [DecidableEq m] [Field L]
  (e : m ≃ n) (K : Subfield L) {A : Matrix m n L} {B : Matrix n m L} (hAB : A * B = 1)

include e hAB

lemma mem_subfield_of_mul_eq_one_of_mem_subfield_left
    (h_mem : ∀ i j, B i j ∈ K) (i : m) (j : n) :
    A i j ∈ K := by
  replace hAB : Bᵀ * Aᵀ = 1 := by simpa using congr_arg transpose hAB
  rw [← A.transpose_apply]
  simp_rw [← B.transpose_apply] at h_mem
  exact mem_subfield_of_mul_eq_one_of_mem_subfield_right e K hAB (fun i j ↦ h_mem j i) j i

end Matrix
