/-
Extracted from Analysis/InnerProductSpace/Laplacian.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Laplacian

This file defines the Laplacian for functions `f : E → F` on real, finite-dimensional, inner product
spaces `E`. In essence, we define the Laplacian of `f` as the second derivative, applied to the
canonical covariant tensor of `E`, as defined and discussed in
`Mathlib.Analysis.InnerProductSpace.CanonicalTensor`.

We show that the Laplacian is `ℝ`-linear on continuously differentiable functions, and establish the
standard formula for computing the Laplacian in terms of orthonormal bases of `E`.
-/

open Filter TensorProduct Topology

section secondDerivativeAPI

/-!
## Supporting API

The definition of the Laplacian of a function `f : E → F` involves the notion of the second
derivative, which can be seen as a continuous multilinear map `ContinuousMultilinearMap 𝕜 (fun (i :
Fin 2) ↦ E) F`, a bilinear map `E →ₗ[𝕜] E →ₗ[𝕜] F`, or a linear map on tensors `E ⊗[𝕜] E →ₗ[𝕜]
F`. This section provides convenience API to convert between these notions.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜) in

noncomputable def bilinearIteratedFDerivWithinTwo (f : E → F) (s : Set E) : E → E →ₗ[𝕜] E →ₗ[𝕜] F :=
  fun x ↦ (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x).toLinearMap₁₂

variable (𝕜) in

noncomputable def bilinearIteratedFDerivTwo (f : E → F) : E → E →ₗ[𝕜] E →ₗ[𝕜] F :=
  fun x ↦ (fderiv 𝕜 (fderiv 𝕜 f) x).toLinearMap₁₂

lemma bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv {e : E} {s : Set E} (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s) (e₁ e₂ : E) :
    bilinearIteratedFDerivWithinTwo 𝕜 f s e e₁ e₂ = iteratedFDerivWithin 𝕜 2 f s e ![e₁, e₂] := by
  simp [iteratedFDerivWithin_two_apply f hs he ![e₁, e₂], bilinearIteratedFDerivWithinTwo]

lemma bilinearIteratedFDerivTwo_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    bilinearIteratedFDerivTwo 𝕜 f e e₁ e₂ = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  simp [iteratedFDeriv_two_apply f e ![e₁, e₂], bilinearIteratedFDerivTwo]

variable (𝕜) in

noncomputable def tensorIteratedFDerivWithinTwo (f : E → F) (s : Set E) : E → E ⊗[𝕜] E →ₗ[𝕜] F :=
  fun e ↦ lift (bilinearIteratedFDerivWithinTwo 𝕜 f s e)

variable (𝕜) in

noncomputable def tensorIteratedFDerivTwo (f : E → F) : E → E ⊗[𝕜] E →ₗ[𝕜] F :=
  fun e ↦ lift (bilinearIteratedFDerivTwo 𝕜 f e)

lemma tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin {e : E} {s : Set E} (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s) (e₁ e₂ : E) :
    tensorIteratedFDerivWithinTwo 𝕜 f s e (e₁ ⊗ₜ[𝕜] e₂) =
      iteratedFDerivWithin 𝕜 2 f s e ![e₁, e₂] := by
  rw [← bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv f hs he, tensorIteratedFDerivWithinTwo,
    lift.tmul]

lemma tensorIteratedFDerivTwo_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    tensorIteratedFDerivTwo 𝕜 f e (e₁ ⊗ₜ[𝕜] e₂) = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, tensorIteratedFDerivTwo, lift.tmul]

end secondDerivativeAPI

/-!
## Definition of the Laplacian
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : E → F} {x : E} {s : Set E}

namespace InnerProductSpace

variable (f s) in

noncomputable def laplacianWithin : E → F :=
  fun x ↦ tensorIteratedFDerivWithinTwo ℝ f s x (InnerProductSpace.canonicalCovariantTensor E)
