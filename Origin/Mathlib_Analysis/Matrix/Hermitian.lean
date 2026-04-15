/-
Extracted from Analysis/Matrix/Hermitian.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Hermitian matrices over ℝ and ℂ

This file proves that Hermitian matrices over ℝ and ℂ are exactly the ones whose corresponding
linear map is self-adjoint.

## Tags

self-adjoint matrix, hermitian matrix
-/

open RCLike

namespace Matrix

variable {𝕜 m n : Type*} {A : Matrix n n 𝕜} [RCLike 𝕜]

lemma IsHermitian.coe_re_apply_self (h : A.IsHermitian) (i : n) : (re (A i i) : 𝕜) = A i i := by
  rw [← conj_eq_iff_re, ← star_def, ← conjTranspose_apply, h.eq]

lemma IsHermitian.coe_re_diag (h : A.IsHermitian) : (fun i => (re (A.diag i) : 𝕜)) = A.diag :=
  funext h.coe_re_apply_self
