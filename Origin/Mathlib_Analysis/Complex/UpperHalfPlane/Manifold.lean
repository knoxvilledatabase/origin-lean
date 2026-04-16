/-
Extracted from Analysis/Complex/UpperHalfPlane/Manifold.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

noncomputable section

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane.
-/

open Filter

open scoped Manifold

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.singletonChartedSpace

instance : SmoothManifoldWithCorners 𝓘(ℂ) ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.singleton_smoothManifoldWithCorners

theorem contMDiff_coe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ ((↑) : ℍ → ℂ) := fun _ => contMDiffAt_extChartAt

theorem mdifferentiable_coe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) :=
  contMDiff_coe.mdifferentiable (by simp)

lemma contMDiffAt_ofComplex {z : ℂ} (hz : 0 < z.im) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ⊤ ofComplex z := by
  rw [contMDiffAt_iff]
  constructor
  · -- continuity at z
    rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa only [ofComplex_apply_of_im_pos hz, Subtype.coe_mk] using tendsto_id
  · -- smoothness in local chart
    simp only [extChartAt, PartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.refl_partialEquiv,
      PartialEquiv.refl_source, PartialHomeomorph.singletonChartedSpace_chartAt_eq,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, CompTriple.comp_eq, modelWithCornersSelf_coe,
      Set.range_id, id_eq, contDiffWithinAt_univ]
    exact contDiffAt_id.congr_of_eventuallyEq (eventuallyEq_coe_comp_ofComplex hz)

lemma mdifferentiableAt_ofComplex {z : ℂ} (hz : 0 < z.im) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ofComplex z :=
  (contMDiffAt_ofComplex hz).mdifferentiableAt (by simp)

lemma mdifferentiableAt_iff {f : ℍ → ℂ} {τ : ℍ} :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f τ ↔ DifferentiableAt ℂ (f ∘ ofComplex) ↑τ := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (mdifferentiableAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (mdifferentiable_coe τ)

lemma mdifferentiable_iff {f : ℍ → ℂ} :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im} :=
  ⟨fun h z hz ↦ (mdifferentiableAt_iff.mp (h ⟨z, hz⟩)).differentiableWithinAt,
    fun h ⟨z, hz⟩ ↦ mdifferentiableAt_iff.mpr <| (h z hz).differentiableAt
      <| (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hz⟩

end UpperHalfPlane
