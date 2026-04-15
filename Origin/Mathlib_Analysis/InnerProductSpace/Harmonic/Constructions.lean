/-
Extracted from Analysis/InnerProductSpace/Harmonic/Constructions.lean
Genuine: 2 of 7 | Dissolved: 2 | Infrastructure: 3
-/
import Origin.Core

/-!
# Construction of Harmonic Functions

This file constructs examples of harmonic functions.

If `f : ℂ → F` is complex-differentiable, then `f` is harmonic. If `F = ℂ`, then so is its real
part, imaginary part, and complex conjugate. If `f` has no zero, then `log ‖f‖` is harmonic.
-/

open Complex ComplexConjugate InnerProductSpace Topology

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : ℂ → F} {x : ℂ}

/-!
## Harmonicity of Analytic Functions on the Complex Plane
-/

set_option backward.isDefEq.respectTransparency false in

theorem ContDiffAt.harmonicAt (h : ContDiffAt ℂ 2 f x) : HarmonicAt f x := by
  refine ⟨h.restrict_scalars ℝ, ?_⟩
  filter_upwards [h.restrictScalars_iteratedFDeriv_eventuallyEq (𝕜 := ℝ)] with a ha
  have : (iteratedFDeriv ℂ 2 f a) (I • ![1, 1])
      = (∏ i, I) • ((iteratedFDeriv ℂ 2 f a) ![1, 1]) :=
    (iteratedFDeriv ℂ 2 f a).map_smul_univ (fun _ ↦ I) ![1, 1]
  simp_all [laplacian_eq_iteratedFDeriv_complexPlane f, ← ha,
    ContinuousMultilinearMap.coe_restrictScalars]

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in

theorem AnalyticAt.harmonicAt_conj {f : ℂ → ℂ} (h : AnalyticAt ℂ f x) : HarmonicAt (conj f) x :=
  (harmonicAt_comp_CLE_iff conjCLE).2 h.harmonicAt

/-!
## Harmonicity of `log ‖analytic‖`
-/

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: analyticAt_harmonicAt_log_normSq

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: AnalyticAt.harmonicAt_log_norm
