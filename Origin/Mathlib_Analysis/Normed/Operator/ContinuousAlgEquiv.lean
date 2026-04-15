/-
Extracted from Analysis/Normed/Operator/ContinuousAlgEquiv.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Continuous (star-)algebra equivalences between continuous endomorphisms are (isometrically) inner

This file shows that continuous (star-)algebra equivalences between continuous endomorphisms are
(isometrically) inner.
See `Mathlib/LinearAlgebra/GeneralLinearGroup/AlgEquiv.lean` for the non-continuous version.
The proof follows the same idea as the non-continuous version.

### TODO:
- when `V = W`, we can state that the group homomorphism
  `(V →L[𝕜] V)ˣ →* ((V →L[𝕜] V) ≃A[𝕜] (V →L[𝕜] V))` is surjective,
  see `Module.End.mulSemiringActionToAlgEquiv_conjAct_surjective` for the non-continuous
  version of this.
-/

open ContinuousLinearMap ContinuousLinearEquiv

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [SeparatingDual 𝕜 V]
  [SeparatingDual 𝕜 W]

variable (𝕜 V W) in

public theorem ContinuousLinearEquiv.conjContinuousAlgEquiv_surjective :
    Function.Surjective (conjContinuousAlgEquiv (𝕜 := 𝕜) (G := V) (H := W)) :=
  fun f ↦ f.eq_continuousLinearEquivConjContinuousAlgEquiv.imp fun _ h ↦ h.symm

end

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

section auxiliaryDefs

variable (e : V ≃L[𝕜] W) {α α' : 𝕜} (hα : α ≠ 0)
  (hα2 : α' * α' = α⁻¹) (he : e.toContinuousLinearMap.adjoint ∘L e = α • .id 𝕜 V)
  (he' : e ∘L e.toContinuousLinearMap.adjoint = α • .id 𝕜 W)

include hα hα2 he he'

noncomputable abbrev auxContinuousLinearEquiv :
    V ≃L[𝕜] W where
  toLinearMap := (α' • e.toContinuousLinearMap).toLinearMap
  invFun := (α' • e.toContinuousLinearMap.adjoint).toLinearMap
  left_inv x := by
    have := by simpa using congr($he x)
    simp [smul_smul, hα2, this, hα, ← mul_assoc]
  right_inv x := by
    have := by simpa using congr($he' x)
    simp [smul_smul, hα2, this, hα, ← mul_assoc]
  continuous_toFun := (α' • e.toContinuousLinearMap).continuous
  continuous_invFun := (α' • e.toContinuousLinearMap.adjoint).continuous
