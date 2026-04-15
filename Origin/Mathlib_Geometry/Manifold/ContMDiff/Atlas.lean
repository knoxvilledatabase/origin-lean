/-
Extracted from Geometry/Manifold/ContMDiff/Atlas.lean
Genuine: 23 of 24 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Smoothness of charts and local structomorphisms

We show that the model with corners, charts, extended charts and their inverses are `C^n`,
and that local structomorphisms are `C^n` with `C^n` inverses.

## Implementation notes

This file uses the name `writtenInExtend` (in analogy to `writtenInExtChart`) to refer to a
composition `ψ.extend J ∘ f ∘ φ.extend I` of `f : M → N` with charts `ψ` and `φ` extended by the
appropriate models with corners. This is not a definition, so technically deviating from the naming
convention.

`isLocalStructomorphOn` is another made-up name.
-/

assert_not_exists mfderiv

open Set ChartedSpace IsManifold

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a `C^n` manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  [IsManifold I n M]
  -- declare a topological space `M'`.
  {M' : Type*} [TopologicalSpace M']
  -- declare functions, sets, points and smoothness indices
  {e : OpenPartialHomeomorph M H} {x : M}

/-! ### Atlas members are `C^n` -/

section Atlas

theorem contMDiff_model : ContMDiff I 𝓘(𝕜, E) n I := by
  intro x
  refine contMDiffAt_iff.mpr ⟨I.continuousAt, ?_⟩
  simp only [mfld_simps]
  refine contDiffWithinAt_id.congr_of_eventuallyEq ?_ ?_
  · exact Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x₂ => I.right_inv
  simp_rw [Function.comp_apply, I.left_inv, Function.id_def]

theorem contMDiffOn_model_symm : ContMDiffOn 𝓘(𝕜, E) I n I.symm (range I) := by
  rw [contMDiffOn_iff]
  refine ⟨I.continuousOn_symm, fun x y => ?_⟩
  simp only [mfld_simps]
  exact contDiffOn_id.congr fun x' => I.right_inv

theorem contMDiffOn_of_mem_maximalAtlas (h : e ∈ maximalAtlas I n M) :
    ContMDiffOn I I n e e.source :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_of_mem_maximalAtlas
    contDiffWithinAtProp_id h

theorem contMDiffOn_symm_of_mem_maximalAtlas (h : e ∈ maximalAtlas I n M) :
    ContMDiffOn I I n e.symm e.target :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_symm_of_mem_maximalAtlas
      contDiffWithinAtProp_id h

theorem contMDiffAt_of_mem_maximalAtlas (h : e ∈ maximalAtlas I n M) (hx : x ∈ e.source) :
    ContMDiffAt I I n e x :=
  (contMDiffOn_of_mem_maximalAtlas h).contMDiffAt <| e.open_source.mem_nhds hx

theorem contMDiffAt_symm_of_mem_maximalAtlas {x : H} (h : e ∈ maximalAtlas I n M)
    (hx : x ∈ e.target) : ContMDiffAt I I n e.symm x :=
  (contMDiffOn_symm_of_mem_maximalAtlas h).contMDiffAt <| e.open_target.mem_nhds hx

theorem contMDiffOn_chart : ContMDiffOn I I n (chartAt H x) (chartAt H x).source :=
  contMDiffOn_of_mem_maximalAtlas <| chart_mem_maximalAtlas x

theorem contMDiffOn_chart_symm : ContMDiffOn I I n (chartAt H x).symm (chartAt H x).target :=
  contMDiffOn_symm_of_mem_maximalAtlas <| chart_mem_maximalAtlas x

theorem contMDiffAt_extend {x : M} (he : e ∈ maximalAtlas I n M) (hx : x ∈ e.source) :
    ContMDiffAt I 𝓘(𝕜, E) n (e.extend I) x :=
  (contMDiff_model _).comp x <| contMDiffAt_of_mem_maximalAtlas he hx

theorem contMDiffOn_extend (he : e ∈ maximalAtlas I n M) :
    ContMDiffOn I 𝓘(𝕜, E) n (e.extend I) e.source :=
  fun _x' hx' ↦ (contMDiffAt_extend he hx').contMDiffWithinAt

theorem contMDiffAt_extChartAt' {x' : M} (h : x' ∈ (chartAt H x).source) :
    ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x' :=
  contMDiffAt_extend (chart_mem_maximalAtlas x) h

omit [IsManifold I n M] in

theorem contMDiffAt_extChartAt : ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x := by
  rw [contMDiffAt_iff_source]
  apply contMDiffWithinAt_id.congr_of_eventuallyEq_of_mem _ (by simp)
  filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
  exact PartialEquiv.right_inv (extChartAt I x) hy

theorem contMDiffOn_extChartAt : ContMDiffOn I 𝓘(𝕜, E) n (extChartAt I x) (chartAt H x).source :=
  fun _x' hx' => (contMDiffAt_extChartAt' hx').contMDiffWithinAt

theorem contMDiffOn_extend_symm (he : e ∈ maximalAtlas I n M) :
    ContMDiffOn 𝓘(𝕜, E) I n (e.extend I).symm (I '' e.target) := by
  refine (contMDiffOn_symm_of_mem_maximalAtlas he).comp
    (contMDiffOn_model_symm.mono <| image_subset_range _ _) ?_
  simp_rw [image_subset_iff, PartialEquiv.restr_coe_symm, I.toPartialEquiv_coe_symm,
    preimage_preimage, I.left_inv, preimage_id']; rfl

theorem contMDiffOn_extChartAt_symm (x : M) :
    ContMDiffOn 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target := by
  convert contMDiffOn_extend_symm (chart_mem_maximalAtlas (I := I) x)
  · rw [extChartAt_target, I.image_eq]
  · infer_instance
  · infer_instance

theorem contMDiffWithinAt_extChartAt_symm_target
    (x : M) {y : E} (hy : y ∈ (extChartAt I x).target) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target y :=
  contMDiffOn_extChartAt_symm x y hy

theorem contMDiffWithinAt_extChartAt_symm_range
    (x : M) {y : E} (hy : y ∈ (extChartAt I x).target) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (range I) y :=
  (contMDiffWithinAt_extChartAt_symm_target x hy).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin_of_mem hy)

omit [IsManifold I n M] in

theorem contMDiffWithinAt_extChartAt_symm_target_self (x : M) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target
      (extChartAt I x x) := by
  rw [contMDiffWithinAt_iff_target]
  constructor
  · apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp _ I.continuousAt_symm
    exact (chartAt H x).symm.continuousAt (by simp)
  · apply contMDiffWithinAt_id.congr_of_mem (fun y hy ↦ ?_) (by simp)
    convert PartialEquiv.right_inv (extChartAt I x) hy
    simp

omit [IsManifold I n M] in

theorem contMDiffWithinAt_extChartAt_symm_range_self (x : M) :
    ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm (range I) (extChartAt I x x) :=
  (contMDiffWithinAt_extChartAt_symm_target_self x).mono_of_mem_nhdsWithin
    (extChartAt_target_mem_nhdsWithin x)

theorem contMDiffOn_of_mem_contDiffGroupoid {e' : OpenPartialHomeomorph H H}
    (h : e' ∈ contDiffGroupoid n I) : ContMDiffOn I I n e' e'.source :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_of_mem_groupoid contDiffWithinAtProp_id h

end Atlas

/-! ### (local) structomorphisms are `C^n` -/

section IsLocalStructomorph

variable [ChartedSpace H M'] [IsM' : IsManifold I n M']

theorem isLocalStructomorphOn_contDiffGroupoid_iff_aux {f : OpenPartialHomeomorph M M'}
    (hf : LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt f f.source) :
    ContMDiffOn I I n f f.source := by
  -- It suffices to show regularity near each `x`
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let c := chartAt H x
  let c' := chartAt H (f x)
  obtain ⟨-, hxf⟩ := hf x hx
  -- Since `f` is a local structomorph, it is locally equal to some transferred element `e` of
  -- the `contDiffGroupoid`.
  obtain
    ⟨e, he, he' : EqOn (c' ∘ f ∘ c.symm) e (c.symm ⁻¹' f.source ∩ e.source), hex :
      c x ∈ e.source⟩ :=
    hxf (by simp only [hx, mfld_simps])
  -- We choose a convenient set `s` in `M`.
  let s : Set M := (f.trans c').source ∩ ((c.trans e).trans c'.symm).source
  refine ⟨s, (f.trans c').open_source.inter ((c.trans e).trans c'.symm).open_source, ?_, ?_⟩
  · simp only [s, mfld_simps]
    rw [← he'] <;> simp only [c, c', hx, hex, mfld_simps]
  -- We need to show `f` is `ContMDiffOn` the domain `s ∩ f.source`.  We show this in two
  -- steps: `f` is equal to `c'.symm ∘ e ∘ c` on that domain and that function is
  -- `ContMDiffOn` it.
  have H₁ : ContMDiffOn I I n (c'.symm ∘ e ∘ c) s := by
    have hc' : ContMDiffOn I I n c'.symm _ := contMDiffOn_chart_symm
    have he'' : ContMDiffOn I I n e _ := contMDiffOn_of_mem_contDiffGroupoid he
    have hc : ContMDiffOn I I n c _ := contMDiffOn_chart
    refine (hc'.comp' (he''.comp' hc)).mono ?_
    dsimp [s, c, c']
    mfld_set_tac
  have H₂ : EqOn f (c'.symm ∘ e ∘ c) s := by
    intro y hy
    simp only [s, mfld_simps] at hy
    have hy₁ : f y ∈ c'.source := by simp only [hy, mfld_simps]
    have hy₂ : y ∈ c.source := by simp only [hy, mfld_simps]
    have hy₃ : c y ∈ c.symm ⁻¹' f.source ∩ e.source := by simp only [hy, mfld_simps]
    calc
      f y = c'.symm (c' (f y)) := by rw [c'.left_inv hy₁]
      _ = c'.symm (c' (f (c.symm (c y)))) := by rw [c.left_inv hy₂]
      _ = c'.symm (e (c y)) := by rw [← he' hy₃]; rfl
  refine (H₁.congr H₂).mono ?_
  mfld_set_tac

end IsLocalStructomorph

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞}
  [IsManifold I n M] [IsManifold J n N] {f : M → N} {s : Set M}
  {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G}

theorem OpenPartialHomeomorph.contMDiffWithinAt_writtenInExtend_iff {y : M}
    (hφ : φ ∈ maximalAtlas I n M) (hψ : ψ ∈ maximalAtlas J n N)
    (hy : y ∈ φ.source) (hgy : f y ∈ ψ.source) (hmaps : MapsTo f s ψ.source) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, F) n (ψ.extend J ∘ f ∘ (φ.extend I).symm)
      ((φ.extend I).symm ⁻¹' s ∩ range I) (φ.extend I y) ↔ ContMDiffWithinAt I J n f s y := by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas hφ hψ hy hgy]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ?_⟩
  · rw [← φ.continuousWithinAt_writtenInExtend_iff (I := I) (I' := J) hy hgy hmaps]
    exact h.continuousWithinAt
  · rwa [← contMDiffWithinAt_iff_contDiffWithinAt]
  · rw [contMDiffWithinAt_iff_contDiffWithinAt]
    exact h.2

theorem OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff
    (hφ : φ ∈ maximalAtlas I n M) (hψ : ψ ∈ maximalAtlas J n N)
    (hs : s ⊆ φ.source) (hmaps : MapsTo f s ψ.source) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n (ψ.extend J ∘ f ∘ (φ.extend I).symm) (φ.extend I '' s) ↔
      ContMDiffOn I J n f s := by
  refine forall_mem_image.trans <| forall₂_congr fun x hx ↦ ?_
  refine (contMDiffWithinAt_congr_set ?_).trans
    (contMDiffWithinAt_writtenInExtend_iff hφ hψ (hs hx) (hmaps hx) hmaps)
  rw [← nhdsWithin_eq_iff_eventuallyEq, ← φ.map_extend_nhdsWithin_eq_image_of_subset,
    ← φ.map_extend_nhdsWithin]
  exacts [hs hx, hs hx, hs]
