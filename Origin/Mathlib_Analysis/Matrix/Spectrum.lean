/-
Extracted from Analysis/Matrix/Spectrum.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Spectral theory of Hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem -/

open WithLp

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

variable {A B : Matrix n n 𝕜}

lemma finite_real_spectrum [DecidableEq n] : (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap 𝕜]
  exact A.finite_spectrum.preimage (FaithfulSMul.algebraMap_injective ℝ 𝕜).injOn

-- INSTANCE (free from Core): [DecidableEq

theorem spectrum_toLpLin [DecidableEq n] (p : ENNReal) :
    spectrum 𝕜 (toLpLin p p A) = spectrum 𝕜 A :=
  AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (PiLp.basisFun p 𝕜 n)) _
