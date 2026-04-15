/-
Extracted from Geometry/Manifold/MFDeriv/UniqueDifferential.lean
Genuine: 11 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Unique derivative sets in manifolds

In this file, we prove various properties of unique derivative sets in manifolds.
* `image_denseRange`: suppose `f` is differentiable on `s` and its derivative at every point of `s`
has dense range. If `s` has the unique differential property, then so does `f '' s`.
* `uniqueMDiffOn_preimage`: the unique differential property is preserved by local diffeomorphisms
* `uniqueDiffOn_target_inter`: the unique differential property is preserved by
  pullbacks of extended charts
* `tangentBundle_proj_preimage`: if `s` has the unique differential property,
  its preimage under the tangent bundle projection also has
-/

noncomputable section

open scoped Manifold

open Set

/-! ### Unique derivative sets in manifolds -/

section UniqueMDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H' M'']
  {s : Set M} {x : M}

section

theorem UniqueMDiffWithinAt.image_denseRange (hs : UniqueMDiffWithinAt I s x)
    {f : M → M'} {f' : E →L[𝕜] E'} (hf : HasMFDerivWithinAt I I' f s x f')
    (hd : DenseRange f') : UniqueMDiffWithinAt I' (f '' s) (f x) := by
  /- Rewrite in coordinates, apply `HasFDerivWithinAt.uniqueDiffWithinAt`. -/
  have := hs.inter' <| hf.1 (extChartAt_source_mem_nhds (I := I') (f x))
  refine (((hf.2.mono ?sub1).uniqueDiffWithinAt this hd).mono ?sub2).congr_pt ?pt
  case pt => simp only [mfld_simps]
  case sub1 => mfld_set_tac
  case sub2 =>
    rintro _ ⟨y, ⟨⟨hys, hfy⟩, -⟩, rfl⟩
    exact ⟨⟨_, hys, ((extChartAt I' (f x)).left_inv hfy).symm⟩, mem_range_self _⟩

theorem UniqueMDiffOn.image_denseRange' (hs : UniqueMDiffOn I s) {f : M → M'}
    {f' : M → E →L[𝕜] E'} (hf : ∀ x ∈ s, HasMFDerivWithinAt I I' f s x (f' x))
    (hd : ∀ x ∈ s, DenseRange (f' x)) :
    UniqueMDiffOn I' (f '' s) :=
  forall_mem_image.2 fun x hx ↦ (hs x hx).image_denseRange (hf x hx) (hd x hx)

theorem UniqueMDiffOn.image_denseRange (hs : UniqueMDiffOn I s) {f : M → M'}
    (hf : MDifferentiableOn I I' f s) (hd : ∀ x ∈ s, DenseRange (mfderivWithin I I' f s x)) :
    UniqueMDiffOn I' (f '' s) :=
  hs.image_denseRange' (fun x hx ↦ (hf x hx).hasMFDerivWithinAt) hd

protected theorem UniqueMDiffWithinAt.preimage_partialHomeomorph (hs : UniqueMDiffWithinAt I s x)
    {e : PartialHomeomorph M M'} (he : e.MDifferentiable I I') (hx : x ∈ e.source) :
    UniqueMDiffWithinAt I' (e.target ∩ e.symm ⁻¹' s) (e x) := by
  rw [← e.image_source_inter_eq', inter_comm]
  exact (hs.inter (e.open_source.mem_nhds hx)).image_denseRange
    (he.mdifferentiableAt hx).hasMFDerivAt.hasMFDerivWithinAt
    (he.mfderiv_surjective hx).denseRange

theorem UniqueMDiffOn.uniqueMDiffOn_preimage (hs : UniqueMDiffOn I s) {e : PartialHomeomorph M M'}
    (he : e.MDifferentiable I I') : UniqueMDiffOn I' (e.target ∩ e.symm ⁻¹' s) := fun _x hx ↦
  e.right_inv hx.1 ▸ (hs _ hx.2).preimage_partialHomeomorph he (e.map_target hx.1)

variable [SmoothManifoldWithCorners I M]  in

theorem UniqueMDiffOn.uniqueDiffOn_target_inter (hs : UniqueMDiffOn I s) (x : M) :
    UniqueDiffOn 𝕜 ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) := by
  -- this is just a reformulation of `UniqueMDiffOn.uniqueMDiffOn_preimage`, using as `e`
  -- the local chart at `x`.
  apply UniqueMDiffOn.uniqueDiffOn
  rw [← PartialEquiv.image_source_inter_eq', inter_comm, extChartAt_source]
  exact (hs.inter (chartAt H x).open_source).image_denseRange'
    (fun y hy ↦ hasMFDerivWithinAt_extChartAt hy.2)
    fun y hy ↦ ((mdifferentiable_chart _).mfderiv_surjective hy.2).denseRange

variable [SmoothManifoldWithCorners I M]  in

theorem UniqueMDiffOn.uniqueDiffOn_inter_preimage (hs : UniqueMDiffOn I s) (x : M) (y : M'')
    {f : M → M''} (hf : ContinuousOn f s) :
    UniqueDiffOn 𝕜
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) :=
  haveI : UniqueMDiffOn I (s ∩ f ⁻¹' (extChartAt I' y).source) := by
    intro z hz
    apply (hs z hz.1).inter'
    apply (hf z hz.1).preimage_mem_nhdsWithin
    exact (isOpen_extChartAt_source y).mem_nhds hz.2
  this.uniqueDiffOn_target_inter _

end

open Bundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {Z : M → Type*}
  [TopologicalSpace (TotalSpace F Z)] [∀ b, TopologicalSpace (Z b)] [∀ b, AddCommMonoid (Z b)]
  [∀ b, Module 𝕜 (Z b)] [FiberBundle F Z] [VectorBundle 𝕜 F Z] [SmoothVectorBundle F Z I]

theorem Trivialization.mdifferentiable (e : Trivialization F (π F Z)) [MemTrivializationAtlas e] :
    e.toPartialHomeomorph.MDifferentiable (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) :=
  ⟨e.contMDiffOn.mdifferentiableOn le_top, e.contMDiffOn_symm.mdifferentiableOn le_top⟩

theorem UniqueMDiffWithinAt.smooth_bundle_preimage {p : TotalSpace F Z}
    (hs : UniqueMDiffWithinAt I s p.proj) :
    UniqueMDiffWithinAt (I.prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) p := by
  set e := trivializationAt F Z p.proj
  have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  have : UniqueMDiffWithinAt (I.prod 𝓘(𝕜, F)) (s ×ˢ univ) (e p) := by
    rw [← Prod.mk.eta (p := e p), FiberBundle.trivializationAt_proj_fst]
    exact hs.prod (uniqueMDiffWithinAt_univ _)
  rw [← e.left_inv hp]
  refine (this.preimage_partialHomeomorph e.mdifferentiable.symm (e.map_source hp)).mono ?_
  rintro y ⟨hy, hys, -⟩
  rwa [PartialHomeomorph.symm_symm, e.coe_coe, e.coe_fst hy] at hys

variable (Z)

theorem UniqueMDiffWithinAt.smooth_bundle_preimage' {b : M} (hs : UniqueMDiffWithinAt I s b)
    (x : Z b) : UniqueMDiffWithinAt (I.prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) ⟨b, x⟩ :=
  hs.smooth_bundle_preimage (p := ⟨b, x⟩)

theorem UniqueMDiffOn.smooth_bundle_preimage (hs : UniqueMDiffOn I s) :
    UniqueMDiffOn (I.prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) := fun _p hp ↦
  (hs _ hp).smooth_bundle_preimage

end UniqueMDiff
