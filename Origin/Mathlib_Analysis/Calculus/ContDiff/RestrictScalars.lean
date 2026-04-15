/-
Extracted from Analysis/Calculus/ContDiff/RestrictScalars.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
### Restricting Scalars in Iterated Fréchet Derivatives

This file establishes standard theorems on restriction of scalars for iterated Fréchet derivatives,
comparing iterated derivatives with respect to a field `𝕜'` to iterated derivatives with respect to
a subfield `𝕜 ⊆ 𝕜'`. The results are analogous to those found in
`Mathlib.Analysis.Calculus.FDeriv.RestrictScalars`.
-/

variable
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : E} {f : E → F} {n : ℕ} {s : Set E}

open ContinuousMultilinearMap Topology

lemma fderivWithin_restrictScalars_comp
    {φ : E → (ContinuousMultilinearMap 𝕜' (fun _ : Fin n ↦ E) F)}
    (h : DifferentiableWithinAt 𝕜' φ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 ((restrictScalars 𝕜) ∘ φ) s x
      = (restrictScalars 𝕜) ∘ ((fderivWithin 𝕜' φ s x).restrictScalars 𝕜) := by
  simp only [← restrictScalarsLinear_apply]
  rw [fderiv_comp_fderivWithin _ (by fun_prop) (h.restrictScalars 𝕜) hs, ContinuousLinearMap.fderiv]
  ext a b
  simp [h.restrictScalars_fderivWithin 𝕜 hs]
