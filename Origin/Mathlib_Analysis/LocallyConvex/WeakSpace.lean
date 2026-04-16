/-
Extracted from Analysis/LocallyConvex/WeakSpace.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.LinearAlgebra.Dual
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Topology.Algebra.Module.WeakDual

noncomputable section

/-! # Closures of convex sets in locally convex spaces

This file contains the standard result that if `E` is a vector space with two locally convex
topologies, then the closure of a convex set is the same in either topology, provided they have the
same collection of continuous linear functionals. In particular, the weak closure of a convex set
in a locally convex space coincides with the closure in the original topology.
Of course, we phrase this in terms of linear maps between locally convex spaces, rather than
creating two separate topologies on the same space.
-/

variable {𝕜 E F : Type*}

variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

variable [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

variable [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜 F] [LocallyConvexSpace ℝ F]

variable (𝕜) in

theorem Convex.toWeakSpace_closure {s : Set E} (hs : Convex ℝ s) :
    (toWeakSpace 𝕜 E) '' (closure s) = closure (toWeakSpace 𝕜 E '' s) := by
  refine le_antisymm (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure
    (Set.compl_subset_compl.mp fun x hx ↦ ?_)
  obtain ⟨x, -, rfl⟩ := (toWeakSpace 𝕜 E).toEquiv.image_compl (closure s) |>.symm.subset hx
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨f, u, hus, hux⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
    hs.closure isClosed_closure (by simpa using hx)
  let f' : WeakSpace 𝕜 E →L[𝕜] 𝕜 :=
    { toLinearMap := (f : E →ₗ[𝕜] 𝕜).comp ((toWeakSpace 𝕜 E).symm : WeakSpace 𝕜 E →ₗ[𝕜] E)
      cont := WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip _ }
  have hux' : u < RCLike.reCLM.comp (f'.restrictScalars ℝ) (toWeakSpace 𝕜 E x) := by simpa [f']
  have hus' : closure (toWeakSpace 𝕜 E '' s) ⊆
      {y | RCLike.reCLM.comp (f'.restrictScalars ℝ) y ≤ u} := by
    refine closure_minimal ?_ <| isClosed_le (by fun_prop) (by fun_prop)
    rintro - ⟨y, hy, rfl⟩
    simpa [f'] using (hus y <| subset_closure hy).le
  exact (hux'.not_le <| hus' ·)

theorem LinearMap.image_closure_of_convex {s : Set E} (hs : Convex ℝ s) (e : E →ₗ[𝕜] F)
    (he : ∀ f : F →L[𝕜] 𝕜, Continuous (e.dualMap f)) :
    e '' (closure s) ⊆ closure (e '' s) := by
  suffices he' : Continuous (toWeakSpace 𝕜 F <| e <| (toWeakSpace 𝕜 E).symm ·) by
    have h_convex : Convex ℝ (e '' s) := hs.linear_image (F := F) e
    rw [← Set.image_subset_image_iff (toWeakSpace 𝕜 F).injective, h_convex.toWeakSpace_closure 𝕜]
    simpa only [Set.image_image, ← hs.toWeakSpace_closure 𝕜, LinearEquiv.symm_apply_apply]
      using he'.continuousOn.image_closure (s := toWeakSpace 𝕜 E '' s)
  exact WeakBilin.continuous_of_continuous_eval _ fun f ↦
    WeakBilin.eval_continuous _ { toLinearMap := e.dualMap f : E →L[𝕜] 𝕜 }

theorem LinearEquiv.image_closure_of_convex {s : Set E} (hs : Convex ℝ s) (e : E ≃ₗ[𝕜] F)
    (he₁ : ∀ f : F →L[𝕜] 𝕜, Continuous (e.dualMap f))
    (he₂ : ∀ f : E →L[𝕜] 𝕜, Continuous (e.symm.dualMap f)) :
    e '' (closure s) = closure (e '' s) := by
  refine le_antisymm ((e : E →ₗ[𝕜] F).image_closure_of_convex hs he₁) ?_
  simp only [Set.le_eq_subset, ← Set.image_subset_image_iff e.symm.injective]
  simpa [Set.image_image]
    using (e.symm : F →ₗ[𝕜] E).image_closure_of_convex (hs.linear_image (e : E →ₗ[𝕜] F)) he₂

theorem LinearEquiv.image_closure_of_convex' {s : Set E} (hs : Convex ℝ s) (e : E ≃ₗ[𝕜] F)
    (e_dual : (F →L[𝕜] 𝕜) ≃ (E →L[𝕜] 𝕜))
    (he : ∀ f : F →L[𝕜] 𝕜, (e_dual f : E →ₗ[𝕜] 𝕜) = e.dualMap f) :
    e '' (closure s) = closure (e '' s) := by
  have he' (f : E →L[𝕜] 𝕜) : (e_dual.symm f : F →ₗ[𝕜] 𝕜) = e.symm.dualMap f := by
    simp only [DFunLike.ext'_iff, ContinuousLinearMap.coe_coe] at he ⊢
    have (g : E →L[𝕜] 𝕜) : ⇑g = e_dual.symm g ∘ e := by
      have := he _ ▸ congr(⇑$(e_dual.apply_symm_apply g)).symm
      simpa
    ext x
    conv_rhs => rw [LinearEquiv.dualMap_apply, ContinuousLinearMap.coe_coe, this]
    simp
  refine e.image_closure_of_convex hs ?_ ?_
  · simpa [← he] using fun f ↦ map_continuous (e_dual f)
  · simpa [← he'] using fun f ↦ map_continuous (e_dual.symm f)
