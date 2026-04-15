/-
Extracted from Geometry/Manifold/VectorBundle/Basic.lean
Genuine: 43 | Conflates: 0 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.FiberwiseLinear
import Mathlib.Topology.VectorBundle.Constructions

/-! # Smooth vector bundles

This file defines smooth vector bundles over a smooth manifold.

Let `E` be a topological vector bundle, with model fiber `F` and base space `B`.  We consider `E` as
carrying a charted space structure given by its trivializations -- these are charts to `B × F`.
Then, by "composition", if `B` is itself a charted space over `H` (e.g. a smooth manifold), then `E`
is also a charted space over `H × F`.

Now, we define `SmoothVectorBundle` as the `Prop` of having smooth transition functions.
Recall the structure groupoid `smoothFiberwiseLinear` on `B × F` consisting of smooth, fiberwise
linear partial homeomorphisms.  We show that our definition of "smooth vector bundle" implies
`HasGroupoid` for this groupoid, and show (by a "composition" of `HasGroupoid` instances) that
this means that a smooth vector bundle is a smooth manifold.

Since `SmoothVectorBundle` is a mixin, it should be easy to make variants and for many such
variants to coexist -- vector bundles can be smooth vector bundles over several different base
fields, they can also be C^k vector bundles, etc.

## Main definitions and constructions

* `FiberBundle.chartedSpace`: A fiber bundle `E` over a base `B` with model fiber `F` is naturally
  a charted space modelled on `B × F`.

* `FiberBundle.chartedSpace'`: Let `B` be a charted space modelled on `HB`.  Then a fiber bundle
  `E` over a base `B` with model fiber `F` is naturally a charted space modelled on `HB.prod F`.

* `SmoothVectorBundle`: Mixin class stating that a (topological) `VectorBundle` is smooth, in the
  sense of having smooth transition functions.

* `SmoothFiberwiseLinear.hasGroupoid`: For a smooth vector bundle `E` over `B` with fiber
  modelled on `F`, the change-of-co-ordinates between two trivializations `e`, `e'` for `E`,
  considered as charts to `B × F`, is smooth and fiberwise linear, in the sense of belonging to the
  structure groupoid `smoothFiberwiseLinear`.

* `Bundle.TotalSpace.smoothManifoldWithCorners`: A smooth vector bundle is naturally a smooth
  manifold.

* `VectorBundleCore.smoothVectorBundle`: If a (topological) `VectorBundleCore` is smooth,
  in the sense of having smooth transition functions (cf. `VectorBundleCore.IsSmooth`),
  then the vector bundle constructed from it is a smooth vector bundle.

* `VectorPrebundle.smoothVectorBundle`: If a `VectorPrebundle` is smooth,
  in the sense of having smooth transition functions (cf. `VectorPrebundle.IsSmooth`),
  then the vector bundle constructed from it is a smooth vector bundle.

* `Bundle.Prod.smoothVectorBundle`: The direct sum of two smooth vector bundles is a smooth vector
  bundle.
-/

open Bundle Set PartialHomeomorph

open Function (id_def)

open Filter

open scoped Manifold Bundle Topology

variable {𝕜 B B' F M : Type*} {E : B → Type*}

/-! ### Charted space structure on a fiber bundle -/

section

variable [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  {HB : Type*} [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

instance FiberBundle.chartedSpace' : ChartedSpace (B × F) (TotalSpace F E) where
  atlas := (fun e : Trivialization F (π F E) => e.toPartialHomeomorph) '' trivializationAtlas F E
  chartAt x := (trivializationAt F E x.proj).toPartialHomeomorph
  mem_chart_source x :=
    (trivializationAt F E x.proj).mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
  chart_mem_atlas _ := mem_image_of_mem _ (trivialization_mem_atlas F E _)

theorem FiberBundle.chartedSpace'_chartAt (x : TotalSpace F E) :
    chartAt (B × F) x = (trivializationAt F E x.proj).toPartialHomeomorph :=
  rfl

instance FiberBundle.chartedSpace : ChartedSpace (ModelProd HB F) (TotalSpace F E) :=
  ChartedSpace.comp _ (B × F) _

theorem FiberBundle.chartedSpace_chartAt (x : TotalSpace F E) :
    chartAt (ModelProd HB F) x =
      (trivializationAt F E x.proj).toPartialHomeomorph ≫ₕ
        (chartAt HB x.proj).prod (PartialHomeomorph.refl F) := by
  dsimp only [chartAt_comp, prodChartedSpace_chartAt, FiberBundle.chartedSpace'_chartAt,
    chartAt_self_eq]
  rw [Trivialization.coe_coe, Trivialization.coe_fst' _ (mem_baseSet_trivializationAt F E x.proj)]

theorem FiberBundle.chartedSpace_chartAt_symm_fst (x : TotalSpace F E) (y : ModelProd HB F)
    (hy : y ∈ (chartAt (ModelProd HB F) x).target) :
    ((chartAt (ModelProd HB F) x).symm y).proj = (chartAt HB x.proj).symm y.1 := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hy ⊢
  exact (trivializationAt F E x.proj).proj_symm_apply hy.2

end

section

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} (E' : B → Type*) [∀ x, Zero (E' x)] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞}

variable [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

protected theorem FiberBundle.extChartAt (x : TotalSpace F E) :
    extChartAt (IB.prod 𝓘(𝕜, F)) x =
      (trivializationAt F E x.proj).toPartialEquiv ≫
        (extChartAt IB x.proj).prod (PartialEquiv.refl F) := by
  simp_rw [extChartAt, FiberBundle.chartedSpace_chartAt, extend]
  simp only [PartialEquiv.trans_assoc, mfld_simps]
  -- Porting note: should not be needed
  rw [PartialEquiv.prod_trans, PartialEquiv.refl_trans]

protected theorem FiberBundle.extChartAt_target (x : TotalSpace F E) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) x).target =
      ((extChartAt IB x.proj).target ∩
        (extChartAt IB x.proj).symm ⁻¹' (trivializationAt F E x.proj).baseSet) ×ˢ univ := by
  rw [FiberBundle.extChartAt, PartialEquiv.trans_target, Trivialization.target_eq, inter_prod]
  rfl

theorem FiberBundle.writtenInExtChartAt_trivializationAt {x : TotalSpace F E} {y}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) x).target) :
    writtenInExtChartAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) x
      (trivializationAt F E x.proj) y = y :=
  writtenInExtChartAt_chartAt_comp _ hy

theorem FiberBundle.writtenInExtChartAt_trivializationAt_symm {x : TotalSpace F E} {y}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) x).target) :
    writtenInExtChartAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (trivializationAt F E x.proj x)
      (trivializationAt F E x.proj).toPartialHomeomorph.symm y = y :=
  writtenInExtChartAt_chartAt_symm_comp _ hy

/-! ### Smoothness of maps in/out fiber bundles

Note: For these results we don't need that the bundle is a smooth vector bundle, or even a vector
bundle at all, just that it is a fiber bundle over a charted base space.
-/

namespace Bundle

theorem contMDiffWithinAt_totalSpace (f : M → TotalSpace F E) {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x => (f x).proj) s x₀ ∧
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) s x₀ := by
  simp (config := { singlePass := true }) only [contMDiffWithinAt_iff_target]
  rw [and_and_and_comm, ← FiberBundle.continuousWithinAt_totalSpace, and_congr_right_iff]
  intro hf
  simp_rw [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    extChartAt_self_apply, modelWithCornersSelf_coe, Function.id_def, ← chartedSpaceSelf_prod]
  refine (contMDiffWithinAt_prod_iff _).trans (and_congr ?_ Iff.rfl)
  have h1 : (fun x => (f x).proj) ⁻¹' (trivializationAt F E (f x₀).proj).baseSet ∈ 𝓝[s] x₀ :=
    ((FiberBundle.continuous_proj F E).continuousWithinAt.comp hf (mapsTo_image f s))
      ((Trivialization.open_baseSet _).mem_nhds (mem_baseSet_trivializationAt F E _))
  refine EventuallyEq.contMDiffWithinAt_iff (eventually_of_mem h1 fun x hx => ?_) ?_
  · simp_rw [Function.comp, PartialHomeomorph.coe_coe, Trivialization.coe_coe]
    rw [Trivialization.coe_fst']
    exact hx
  · simp only [mfld_simps]

theorem contMDiffAt_totalSpace (f : M → TotalSpace F E) (x₀ : M) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x => (f x).proj) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, F) n (fun x => (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]; exact contMDiffWithinAt_totalSpace f

theorem contMDiffWithinAt_section (s : ∀ x, E x) (a : Set B) (x₀ : B) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) a x₀ ↔
      ContMDiffWithinAt IB 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F E x₀ ⟨x, s x⟩).2) a x₀ := by
  simp_rw [contMDiffWithinAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffWithinAt_id

theorem contMDiffAt_section (s : ∀ x, E x) (x₀ : B) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x₀ ↔
      ContMDiffAt IB 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F E x₀ ⟨x, s x⟩).2) x₀ := by
  simp_rw [contMDiffAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffAt_id

variable (E)

theorem contMDiff_proj : ContMDiff (IB.prod 𝓘(𝕜, F)) IB n (π F E) := fun x ↦ by
  have : ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n id x := contMDiffAt_id
  rw [contMDiffAt_totalSpace] at this
  exact this.1

theorem contMDiffOn_proj {s : Set (TotalSpace F E)} :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) IB n (π F E) s :=
  (Bundle.contMDiff_proj E).contMDiffOn

theorem contMDiffAt_proj {p : TotalSpace F E} : ContMDiffAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) p :=
  (Bundle.contMDiff_proj E).contMDiffAt

theorem contMDiffWithinAt_proj {s : Set (TotalSpace F E)} {p : TotalSpace F E} :
    ContMDiffWithinAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) s p :=
  (Bundle.contMDiffAt_proj E).contMDiffWithinAt

variable (𝕜) [∀ x, AddCommMonoid (E x)]

variable [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E]

theorem contMDiff_zeroSection : ContMDiff IB (IB.prod 𝓘(𝕜, F)) ⊤ (zeroSection F E) := fun x ↦ by
  unfold zeroSection
  rw [Bundle.contMDiffAt_section]
  apply (contMDiffAt_const (c := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
    using congr_arg Prod.snd <| (trivializationAt F E x).zeroSection 𝕜 hy

end Bundle

end

/-! ### Smooth vector bundles -/

variable [NontriviallyNormedField 𝕜] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {EM : Type*} [NormedAddCommGroup EM]
  [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section WithTopology

variable [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] (F E)

variable [FiberBundle F E] [VectorBundle 𝕜 F E]

variable (IB) in

class SmoothVectorBundle : Prop where
  protected contMDiffOn_coordChangeL :
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) ⊤ (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
        (e.baseSet ∩ e'.baseSet)

variable [SmoothVectorBundle F E IB]

section SmoothCoordChange

variable {F E}

variable (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']

theorem contMDiffOn_coordChangeL :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) :=
  (SmoothVectorBundle.contMDiffOn_coordChangeL e e').of_le le_top

theorem contMDiffOn_symm_coordChangeL :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b : B => ((e.coordChangeL 𝕜 e' b).symm : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) := by
  apply ContMDiffOn.of_le _ le_top
  rw [inter_comm]
  refine (SmoothVectorBundle.contMDiffOn_coordChangeL e' e).congr fun b hb ↦ ?_
  rw [e.symm_coordChangeL e' hb]

alias smoothOn_symm_coordChangeL := contMDiffOn_symm_coordChangeL

variable {e e'}

theorem contMDiffAt_coordChangeL {x : B} (h : x ∈ e.baseSet) (h' : x ∈ e'.baseSet) :
    ContMDiffAt IB 𝓘(𝕜, F →L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) x :=
  (contMDiffOn_coordChangeL e e').contMDiffAt <|
    (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨h, h'⟩

variable {s : Set M} {f : M → B} {g : M → F} {x : M}

protected theorem ContMDiffWithinAt.coordChangeL
    (hf : ContMDiffWithinAt IM IB n f s x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    ContMDiffWithinAt IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s x :=
  (contMDiffAt_coordChangeL he he').comp_contMDiffWithinAt _ hf

protected nonrec theorem ContMDiffAt.coordChangeL
    (hf : ContMDiffAt IM IB n f x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) x :=
  hf.coordChangeL he he'

protected theorem ContMDiffOn.coordChangeL
    (hf : ContMDiffOn IM IB n f s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    ContMDiffOn IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s :=
  fun x hx ↦ (hf x hx).coordChangeL (he hx) (he' hx)

protected theorem ContMDiff.coordChangeL
    (hf : ContMDiff IM IB n f) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    ContMDiff IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) := fun x ↦
  (hf x).coordChangeL (he x) (he' x)

alias SmoothWithinAt.coordChangeL := ContMDiffWithinAt.coordChangeL

alias SmoothAt.coordChangeL := ContMDiffAt.coordChangeL

alias SmoothOn.coordChangeL := ContMDiffOn.coordChangeL

alias Smooth.coordChangeL := ContMDiff.coordChangeL

protected theorem ContMDiffWithinAt.coordChange
    (hf : ContMDiffWithinAt IM IB n f s x) (hg : ContMDiffWithinAt IM 𝓘(𝕜, F) n g s x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) s x := by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  · have : e.baseSet ∩ e'.baseSet ∈ 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    exact (Trivialization.coordChangeL_apply' e e' hy (g y)).symm
  · exact (Trivialization.coordChangeL_apply' e e' ⟨he, he'⟩ (g x)).symm

protected nonrec theorem ContMDiffAt.coordChange
    (hf : ContMDiffAt IM IB n f x) (hg : ContMDiffAt IM 𝓘(𝕜, F) n g x) (he : f x ∈ e.baseSet)
    (he' : f x ∈ e'.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) x :=
  hf.coordChange hg he he'

protected theorem ContMDiffOn.coordChange (hf : ContMDiffOn IM IB n f s)
    (hg : ContMDiffOn IM 𝓘(𝕜, F) n g s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    ContMDiffOn IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) s := fun x hx ↦
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)

protected theorem ContMDiff.coordChange (hf : ContMDiff IM IB n f)
    (hg : ContMDiff IM 𝓘(𝕜, F) n g) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    ContMDiff IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) := fun x ↦
  (hf x).coordChange (hg x) (he x) (he' x)

alias SmoothWithinAt.coordChange := ContMDiffWithinAt.coordChange

alias SmoothAt.coordChange := ContMDiffAt.coordChange

alias SmoothOn.coordChange := ContMDiffOn.coordChange

alias Smooth.coordChange := ContMDiff.coordChange

variable (e e')

variable (IB) in

theorem Trivialization.contMDiffOn_symm_trans :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (e.toPartialHomeomorph.symm ≫ₕ e'.toPartialHomeomorph) (e.target ∩ e'.target) := by
  have Hmaps : MapsTo Prod.fst (e.target ∩ e'.target) (e.baseSet ∩ e'.baseSet) := fun x hx ↦
    ⟨e.mem_target.1 hx.1, e'.mem_target.1 hx.2⟩
  rw [mapsTo_inter] at Hmaps
  -- TODO: drop `congr` https://github.com/leanprover-community/mathlib4/issues/5473
  refine (contMDiffOn_fst.prod_mk
    (contMDiffOn_fst.coordChange contMDiffOn_snd Hmaps.1 Hmaps.2)).congr ?_
  rintro ⟨b, x⟩ hb
  refine Prod.ext ?_ rfl
  have : (e.toPartialHomeomorph.symm (b, x)).1 ∈ e'.baseSet := by
    simp_all only [Trivialization.mem_target, mfld_simps]
  exact (e'.coe_fst' this).trans (e.proj_symm_apply hb.1)

variable {e e'}

theorem ContMDiffWithinAt.change_section_trivialization {f : M → TotalSpace F E}
    (hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x)
    (hf : ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e (f y)).2) s x)
    (he : f x ∈ e.source) (he' : f x ∈ e'.source) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e' (f y)).2) s x := by
  rw [Trivialization.mem_source] at he he'
  refine (hp.coordChange hf he he').congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hp.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
    rw [Function.comp_apply, e.coordChange_apply_snd _ hy]
  · rw [Function.comp_apply, e.coordChange_apply_snd _ he]

theorem Trivialization.contMDiffWithinAt_snd_comp_iff₂ {f : M → TotalSpace F E}
    (hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x)
    (he : f x ∈ e.source) (he' : f x ∈ e'.source) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e (f y)).2) s x ↔
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e' (f y)).2) s x :=
  ⟨(hp.change_section_trivialization · he he'), (hp.change_section_trivialization · he' he)⟩

end SmoothCoordChange

variable [SmoothManifoldWithCorners IB B] in

instance SmoothFiberwiseLinear.hasGroupoid :
    HasGroupoid (TotalSpace F E) (smoothFiberwiseLinear B F IB) where
  compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    haveI : MemTrivializationAtlas e := ⟨he⟩
    haveI : MemTrivializationAtlas e' := ⟨he'⟩
    rw [mem_smoothFiberwiseLinear_iff]
    refine ⟨_, _, e.open_baseSet.inter e'.open_baseSet, contMDiffOn_coordChangeL e e',
      contMDiffOn_symm_coordChangeL e e', ?_⟩
    refine PartialHomeomorph.eqOnSourceSetoid.symm ⟨?_, ?_⟩
    · simp only [e.symm_trans_source_eq e', FiberwiseLinear.partialHomeomorph, trans_toPartialEquiv,
        symm_toPartialEquiv]
    · rintro ⟨b, v⟩ hb
      exact (e.apply_symm_apply_eq_coordChangeL e' hb.1 v).symm

variable [SmoothManifoldWithCorners IB B] in

instance Bundle.TotalSpace.smoothManifoldWithCorners [SmoothManifoldWithCorners IB B] :
    SmoothManifoldWithCorners (IB.prod 𝓘(𝕜, F)) (TotalSpace F E) := by
  refine { StructureGroupoid.HasGroupoid.comp (smoothFiberwiseLinear B F IB) ?_ with }
  intro e he
  rw [mem_smoothFiberwiseLinear_iff] at he
  obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  refine ⟨ContMDiffOn.congr ?_ (EqOnSource.eqOn heφ),
      ContMDiffOn.congr ?_ (EqOnSource.eqOn (EqOnSource.symm' heφ))⟩
  · rw [EqOnSource.source_eq heφ]
    apply contMDiffOn_fst.prod_mk
    exact (hφ.comp contMDiffOn_fst <| prod_subset_preimage_fst _ _).clm_apply contMDiffOn_snd
  · rw [EqOnSource.target_eq heφ]
    apply contMDiffOn_fst.prod_mk
    exact (h2φ.comp contMDiffOn_fst <| prod_subset_preimage_fst _ _).clm_apply contMDiffOn_snd

section

variable {F E}

variable {e e' : Trivialization F (π F E)} [MemTrivializationAtlas e] [MemTrivializationAtlas e']

theorem Trivialization.contMDiffWithinAt_iff {f : M → TotalSpace F E} {s : Set M} {x₀ : M}
    (he : f x₀ ∈ e.source) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x => (f x).proj) s x₀ ∧
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) s x₀ :=
  (contMDiffWithinAt_totalSpace _).trans <| and_congr_right fun h ↦
    Trivialization.contMDiffWithinAt_snd_comp_iff₂ h FiberBundle.mem_trivializationAt_proj_source he

theorem Trivialization.contMDiffAt_iff {f : M → TotalSpace F E} {x₀ : M} (he : f x₀ ∈ e.source) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x => (f x).proj) x₀ ∧
      ContMDiffAt IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) x₀ :=
  e.contMDiffWithinAt_iff he

theorem Trivialization.contMDiffOn_iff {f : M → TotalSpace F E} {s : Set M}
    (he : MapsTo f s e.source) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n f s ↔
      ContMDiffOn IM IB n (fun x => (f x).proj) s ∧
      ContMDiffOn IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) s := by
  simp only [ContMDiffOn, ← forall_and]
  exact forall₂_congr fun x hx ↦ e.contMDiffWithinAt_iff (he hx)

theorem Trivialization.contMDiff_iff {f : M → TotalSpace F E} (he : ∀ x, f x ∈ e.source) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F)) n f ↔
      ContMDiff IM IB n (fun x => (f x).proj) ∧
      ContMDiff IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) :=
  (forall_congr' fun x ↦ e.contMDiffAt_iff (he x)).trans forall_and

alias Trivialization.smoothWithinAt_iff := Trivialization.contMDiffWithinAt_iff

alias Trivialization.smoothAt_iff := Trivialization.contMDiffAt_iff

alias Trivialization.smoothOn_iff := Trivialization.contMDiffOn_iff

alias Trivialization.smooth_iff := Trivialization.contMDiff_iff

theorem Trivialization.contMDiffOn (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) ⊤ e e.source := by
  have : ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) ⊤ id e.source := contMDiffOn_id
  rw [e.contMDiffOn_iff (mapsTo_id _)] at this
  exact (this.1.prod_mk this.2).congr fun x hx ↦ (e.mk_proj_snd hx).symm

theorem Trivialization.contMDiffOn_symm (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) ⊤ e.toPartialHomeomorph.symm e.target := by
  rw [e.contMDiffOn_iff e.toPartialHomeomorph.symm_mapsTo]
  refine ⟨contMDiffOn_fst.congr fun x hx ↦ e.proj_symm_apply hx,
    contMDiffOn_snd.congr fun x hx ↦ ?_⟩
  rw [e.apply_symm_apply hx]

alias Trivialization.smoothOn_symm := Trivialization.contMDiffOn_symm

end

/-! ### Core construction for smooth vector bundles -/

namespace VectorBundleCore

variable {F}

variable {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι)

class IsSmooth (IB : ModelWithCorners 𝕜 EB HB) : Prop where
  contMDiffOn_coordChange :
    ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) ⊤ (Z.coordChange i j) (Z.baseSet i ∩ Z.baseSet j)

theorem contMDiffOn_coordChange (IB : ModelWithCorners 𝕜 EB HB) [h : Z.IsSmooth IB] (i j : ι) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) ⊤ (Z.coordChange i j) (Z.baseSet i ∩ Z.baseSet j) :=
  h.1 i j

alias smoothOn_coordChange := contMDiffOn_coordChange

variable [Z.IsSmooth IB]

instance smoothVectorBundle : SmoothVectorBundle F Z.Fiber IB where
  contMDiffOn_coordChangeL := by
    rintro - - ⟨i, rfl⟩ ⟨i', rfl⟩
    refine (Z.contMDiffOn_coordChange IB i i').congr fun b hb ↦ ?_
    ext v
    exact Z.localTriv_coordChange_eq i i' hb v

end VectorBundleCore

/-! ### The trivial smooth vector bundle -/

instance Bundle.Trivial.smoothVectorBundle : SmoothVectorBundle F (Bundle.Trivial B F) IB where
  contMDiffOn_coordChangeL := by
    intro e e' he he'
    obtain rfl := Bundle.Trivial.eq_trivialization B F e
    obtain rfl := Bundle.Trivial.eq_trivialization B F e'
    simp_rw [Bundle.Trivial.trivialization.coordChangeL]
    exact contMDiff_const.contMDiffOn

/-! ### Direct sums of smooth vector bundles -/

section Prod

variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B → Type*)
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]

variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B → Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]

variable [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂] [SmoothVectorBundle F₁ E₁ IB]
  [SmoothVectorBundle F₂ E₂ IB]

variable [SmoothManifoldWithCorners IB B]

instance Bundle.Prod.smoothVectorBundle : SmoothVectorBundle (F₁ × F₂) (E₁ ×ᵇ E₂) IB where
  contMDiffOn_coordChangeL := by
    rintro _ _ ⟨e₁, e₂, i₁, i₂, rfl⟩ ⟨e₁', e₂', i₁', i₂', rfl⟩
    refine ContMDiffOn.congr ?_ (e₁.coordChangeL_prod 𝕜 e₁' e₂ e₂')
    refine ContMDiffOn.clm_prodMap ?_ ?_
    · refine (contMDiffOn_coordChangeL e₁ e₁').mono ?_
      simp only [Trivialization.baseSet_prod, mfld_simps]
      mfld_set_tac
    · refine (contMDiffOn_coordChangeL e₂ e₂').mono ?_
      simp only [Trivialization.baseSet_prod, mfld_simps]
      mfld_set_tac

end Prod

end WithTopology

/-! ### Prebundle construction for smooth vector bundles -/

namespace VectorPrebundle

variable [∀ x, TopologicalSpace (E x)]

variable (IB) in

class IsSmooth (a : VectorPrebundle 𝕜 F E) : Prop where
  exists_smoothCoordChange :
    ∀ᵉ (e ∈ a.pretrivializationAtlas) (e' ∈ a.pretrivializationAtlas),
      ∃ f : B → F →L[𝕜] F,
        ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) ⊤ f (e.baseSet ∩ e'.baseSet) ∧
          ∀ (b : B) (_ : b ∈ e.baseSet ∩ e'.baseSet) (v : F),
            f b v = (e' ⟨b, e.symm b v⟩).2

variable (a : VectorPrebundle 𝕜 F E) [ha : a.IsSmooth IB] {e e' : Pretrivialization F (π F E)}

variable (IB) in

noncomputable def smoothCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) (b : B) : F →L[𝕜] F :=
  Classical.choose (ha.exists_smoothCoordChange e he e' he') b

theorem contMDiffOn_smoothCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) ⊤ (a.smoothCoordChange IB he he') (e.baseSet ∩ e'.baseSet) :=
  (Classical.choose_spec (ha.exists_smoothCoordChange e he e' he')).1

alias smoothOn_smoothCoordChange := contMDiffOn_smoothCoordChange

theorem smoothCoordChange_apply (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    a.smoothCoordChange IB he he' b v = (e' ⟨b, e.symm b v⟩).2 :=
  (Classical.choose_spec (ha.exists_smoothCoordChange e he e' he')).2 b hb v

theorem mk_smoothCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    (b, a.smoothCoordChange IB he he' b v) = e' ⟨b, e.symm b v⟩ := by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]; exact hb.2
  · exact a.smoothCoordChange_apply he he' hb v

variable (IB) in

theorem smoothVectorBundle : @SmoothVectorBundle
    _ _ F E _ _ _ _ _ _ IB _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle a.toVectorBundle :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle; letI := a.toVectorBundle
  { contMDiffOn_coordChangeL := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.contMDiffOn_smoothCoordChange he he').congr ?_
      intro b hb
      ext v
      rw [a.smoothCoordChange_apply he he' hb v, ContinuousLinearEquiv.coe_coe,
        Trivialization.coordChangeL_apply]
      exacts [rfl, hb] }

end VectorPrebundle
