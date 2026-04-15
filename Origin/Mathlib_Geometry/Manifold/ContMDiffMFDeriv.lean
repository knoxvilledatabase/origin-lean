/-
Extracted from Geometry/Manifold/ContMDiffMFDeriv.lean
Genuine: 13 of 14 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
### Interactions between differentiability, smoothness and manifold derivatives

We give the relation between `MDifferentiable`, `ContMDiff`, `mfderiv`, `tangentMap`
and related notions.

## Main statements

* `ContMDiffOn.contMDiffOn_tangentMapWithin` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `ContMDiff.contMDiff_tangentMap` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
-/

open Set Function Filter ChartedSpace IsManifold Bundle

open scoped Topology Manifold Bundle

/-! ### Definition of `C^n` functions between manifolds -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m n : WithTop ℕ∞}
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a `C^n` manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [Js : IsManifold J 1 N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- declare functions, sets
  {f : M → M'} {s : Set M}

/-! ### The derivative of a `C^(n+1)` function is `C^n` -/

section mfderiv

variable [Is : IsManifold I 1 M] [I's : IsManifold I' 1 M']

protected theorem ContMDiffWithinAt.mfderivWithin {x₀ : N} {f : N → M → M'} {g : N → M}
    {t : Set N} {u : Set M}
    (hf : CMDiffAt[t ×ˢ u] n (Function.uncurry f) (x₀, g x₀))
    (hg : CMDiffAt[t] m g x₀) (hx₀ : x₀ ∈ t)
    (hu : MapsTo g t u) (hmn : m + 1 ≤ n) (h'u : UniqueMDiffOn I u) :
    CMDiffAt[t] m (inTangentCoordinates I I' g (fun x ↦ f x (g x))
      (fun x ↦ mfderiv[u] (f x) (g x)) x₀) x₀ := by
  -- first localize the result to a smaller set, to make sure everything happens in chart domains
  let t' := t ∩ g ⁻¹' ((extChartAt I (g x₀)).source)
  have ht't : t' ⊆ t := inter_subset_left
  suffices CMDiffAt[t'] m (inTangentCoordinates I I' g (fun x ↦ f x (g x))
      (fun x ↦ mfderiv[u] (f x) (g x)) x₀) x₀ by
    apply ContMDiffWithinAt.mono_of_mem_nhdsWithin this
    apply inter_mem self_mem_nhdsWithin
    exact hg.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (g x₀))
  -- register a few basic facts that maps send suitable neighborhoods to suitable neighborhoods,
  -- by continuity
  have hx₀gx₀ : (x₀, g x₀) ∈ t ×ˢ u := by simp [hx₀, hu hx₀]
  have h4f : ContinuousWithinAt (fun x ↦ f x (g x)) t x₀ := by
    change ContinuousWithinAt ((Function.uncurry f) ∘ (fun x ↦ (x, g x))) t x₀
    refine ContinuousWithinAt.comp hf.continuousWithinAt ?_ (fun y hy ↦ by simp [hy, hu hy])
    exact (continuousWithinAt_id.prodMk hg.continuousWithinAt)
  have h4f := h4f.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (I := I') (f x₀ (g x₀)))
  have h3f := (contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin (by simp)).mp
    (hf.of_le <| (self_le_add_left 1 m).trans hmn)
  simp only [hx₀gx₀, insert_eq_of_mem] at h3f
  have h2f : ∀ᶠ x₂ in 𝓝[t] x₀, CMDiffAt[u] 1 (f x₂) (g x₂) := by
    have : MapsTo (fun x ↦ (x, g x)) t (t ×ˢ u) := fun y hy ↦ by simp [hy, hu hy]
    filter_upwards [((continuousWithinAt_id.prodMk hg.continuousWithinAt)
      |>.tendsto_nhdsWithin this).eventually h3f, self_mem_nhdsWithin] with x hx h'x
    apply hx.comp (g x) (contMDiffWithinAt_const.prodMk contMDiffWithinAt_id)
    exact fun y hy ↦ by simp [h'x, hy]
  have h2g : g ⁻¹' (extChartAt I (g x₀)).source ∈ 𝓝[t] x₀ :=
    hg.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (g x₀))
  -- key point: the derivative of `f` composed with extended charts, at the point `g x` read in the
  -- chart, is `C^n` in the vector space sense. This follows from `ContDiffWithinAt.fderivWithin`,
  -- which is the vector space analogue of the result we are proving.
  have : ContDiffWithinAt 𝕜 m (fun x ↦ fderivWithin 𝕜
        (extChartAt I' (f x₀ (g x₀)) ∘ f ((extChartAt J x₀).symm x) ∘ (extChartAt I (g x₀)).symm)
        ((extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u)
        (extChartAt I (g x₀) (g ((extChartAt J x₀).symm x))))
      ((extChartAt J x₀).symm ⁻¹' t' ∩ range J) (extChartAt J x₀ x₀) := by
    have hf' := hf.mono (prod_mono_left ht't)
    have hg' := hg.mono (show t' ⊆ t from inter_subset_left)
    rw [contMDiffWithinAt_iff] at hf' hg'
    simp_rw [Function.comp_def, uncurry, extChartAt_prod, PartialEquiv.prod_coe_symm,
      ModelWithCorners.range_prod] at hf' ⊢
    apply ContDiffWithinAt.fderivWithin _ _ _ (show (m : WithTop ℕ∞) + 1 ≤ n from mod_cast hmn)
    · simp [hx₀, t']
    · apply inter_subset_left.trans
      rw [preimage_subset_iff]
      intro a ha
      refine ⟨PartialEquiv.map_source _ (inter_subset_right ha :), ?_⟩
      rw [mem_preimage, PartialEquiv.left_inv (extChartAt I (g x₀))]
      · exact hu (inter_subset_left ha)
      · exact (inter_subset_right ha :)
    · have : ((fun p ↦ ((extChartAt J x₀).symm p.1, (extChartAt I (g x₀)).symm p.2)) ⁻¹' t' ×ˢ u
            ∩ range J ×ˢ (extChartAt I (g x₀)).target)
          ⊆ ((fun p ↦ ((extChartAt J x₀).symm p.1, (extChartAt I (g x₀)).symm p.2)) ⁻¹' t' ×ˢ u
            ∩ range J ×ˢ range I) := by
        apply inter_subset_inter_right
        exact Set.prod_mono_right (extChartAt_target_subset_range (g x₀))
      convert hf'.2.mono this
      · ext y; simp; tauto
      · simp
    · exact hg'.2
    · exact UniqueMDiffOn.uniqueDiffOn_target_inter h'u (g x₀)
  -- reformulate the previous point as `C^n` in the manifold sense (but still for a map between
  -- vector spaces)
  have : CMDiffAt[t'] m
      (fun x ↦ fderivWithin 𝕜 (extChartAt I' (f x₀ (g x₀)) ∘ f x ∘ (extChartAt I (g x₀)).symm)
      ((extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u)
        (extChartAt I (g x₀) (g x))) x₀ := by
    simp_rw [contMDiffWithinAt_iff_source (x := x₀),
      contMDiffWithinAt_iff_contDiffWithinAt, Function.comp_def]
    exact this
  -- finally, argue that the map we control in the previous point coincides locally with the map we
  -- want to prove the regularity of, so regularity of the latter follows from regularity of the
  -- former.
  apply this.congr_of_eventuallyEq_of_mem _ (by simp [t', hx₀])
  apply nhdsWithin_mono _ ht't
  filter_upwards [h2f, h4f, h2g, self_mem_nhdsWithin] with x hx h'x h2 hxt
  have h1 : g x ∈ u := hu hxt
  have h3 : UniqueMDiffWithinAt 𝓘(𝕜, E)
      ((extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u)
      ((extChartAt I (g x₀)) (g x)) := by
    apply UniqueDiffWithinAt.uniqueMDiffWithinAt
    apply UniqueMDiffOn.uniqueDiffOn_target_inter h'u
    refine ⟨PartialEquiv.map_source _ h2, ?_⟩
    rwa [mem_preimage, PartialEquiv.left_inv _ h2]
  have A : mfderiv[range I] ((extChartAt I (g x₀)).symm) ((extChartAt I (g x₀)) (g x))
      = mfderiv[(extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u]
        ((extChartAt I (g x₀)).symm) ((extChartAt I (g x₀)) (g x)) := by
    apply (MDifferentiableWithinAt.mfderivWithin_mono _ h3 _).symm
    · apply mdifferentiableWithinAt_extChartAt_symm
      exact PartialEquiv.map_source (extChartAt I (g x₀)) h2
    · exact inter_subset_left.trans (extChartAt_target_subset_range (g x₀))
  rw [inTangentCoordinates_eq_mfderiv_comp, A,
    ← mfderivWithin_comp_of_eq, ← mfderiv_comp_mfderivWithin_of_eq]
  · exact mfderivWithin_eq_fderivWithin
  · exact mdifferentiableAt_extChartAt (by simpa using h'x)
  · apply MDifferentiableWithinAt.comp (I' := I) (u := u) _ _ _ inter_subset_right
    · convert hx.mdifferentiableWithinAt one_ne_zero
      exact PartialEquiv.left_inv (extChartAt I (g x₀)) h2
    · apply (mdifferentiableWithinAt_extChartAt_symm _).mono
      · exact inter_subset_left.trans (extChartAt_target_subset_range (g x₀))
      · exact PartialEquiv.map_source (extChartAt I (g x₀)) h2
  · exact h3
  · simp only [Function.comp_def, PartialEquiv.left_inv (extChartAt I (g x₀)) h2]
  · exact hx.mdifferentiableWithinAt one_ne_zero
  · apply (mdifferentiableWithinAt_extChartAt_symm _).mono
    · exact inter_subset_left.trans (extChartAt_target_subset_range (g x₀))
    · exact PartialEquiv.map_source (extChartAt I (g x₀)) h2
  · exact inter_subset_right
  · exact h3
  · exact PartialEquiv.left_inv (extChartAt I (g x₀)) h2
  · simpa using h2
  · simpa using h'x

theorem ContMDiffWithinAt.mfderivWithin_const {x₀ : M} {f : M → M'}
    (hf : CMDiffAt[s] n f x₀) (hmn : m + 1 ≤ n) (hx : x₀ ∈ s) (hs : UniqueMDiffOn I s) :
    CMDiffAt[s] m (inTangentCoordinates I I' id f (mfderiv[s] f) x₀) x₀ := by
  have : CMDiffAt[s ×ˢ s] n (fun x : M × M ↦ f x.2) (x₀, x₀) :=
    hf.comp (x₀, x₀) contMDiffWithinAt_snd mapsTo_snd_prod
  exact this.mfderivWithin contMDiffWithinAt_id hx (mapsTo_id _) hmn hs

theorem ContMDiffWithinAt.mfderivWithin_apply {x₀ : N'}
    {f : N → M → M'} {g : N → M} {g₁ : N' → N} {g₂ : N' → E} {t : Set N} {u : Set M} {v : Set N'}
    (hf : CMDiffAt[t ×ˢ u] n (Function.uncurry f) (g₁ x₀, g (g₁ x₀)))
    (hg : CMDiffAt[t] m g (g₁ x₀)) (hg₁ : CMDiffAt[v] m g₁ x₀)
    (hg₂ : CMDiffAt[v] m g₂ x₀) (hmn : m + 1 ≤ n) (h'g₁ : MapsTo g₁ v t)
    (hg₁x₀ : g₁ x₀ ∈ t) (h'g : MapsTo g t u) (hu : UniqueMDiffOn I u) :
    CMDiffAt[v] m (fun x ↦ (inTangentCoordinates I I' g (fun x ↦ f x (g x))
      (fun x ↦ mfderiv[u] (f x) (g x)) (g₁ x₀) (g₁ x)) (g₂ x)) x₀ :=
  ((hf.mfderivWithin hg hg₁x₀ h'g hmn hu).comp_of_eq hg₁ h'g₁ rfl).clm_apply hg₂

protected theorem ContMDiffAt.mfderiv {x₀ : N} (f : N → M → M') (g : N → M)
    (hf : CMDiffAt n (Function.uncurry f) (x₀, g x₀)) (hg : CMDiffAt m g x₀)
    (hmn : m + 1 ≤ n) :
    CMDiffAt m
      (inTangentCoordinates I I' g (fun x ↦ f x (g x)) (fun x ↦ mfderiv% (f x) (g x)) x₀) x₀ := by
  rw [← contMDiffWithinAt_univ] at hf hg ⊢
  rw [← univ_prod_univ] at hf
  simp_rw [← mfderivWithin_univ]
  exact ContMDiffWithinAt.mfderivWithin hf hg (mem_univ _) (mapsTo_univ _ _) hmn
    uniqueMDiffOn_univ

theorem ContMDiffAt.mfderiv_const {x₀ : M} {f : M → M'} (hf : CMDiffAt n f x₀)
    (hmn : m + 1 ≤ n) :
    CMDiffAt m (inTangentCoordinates I I' id f (mfderiv% f) x₀) x₀ :=
  haveI : CMDiffAt n (fun x : M × M ↦ f x.2) (x₀, x₀) :=
    ContMDiffAt.comp (x₀, x₀) hf contMDiffAt_snd
  this.mfderiv (fun _ ↦ f) id contMDiffAt_id hmn

theorem ContMDiffAt.mfderiv_apply {x₀ : N'} (f : N → M → M') (g : N → M) (g₁ : N' → N) (g₂ : N' → E)
    (hf : CMDiffAt n (Function.uncurry f) (g₁ x₀, g (g₁ x₀)))
    (hg : CMDiffAt m g (g₁ x₀)) (hg₁ : CMDiffAt m g₁ x₀) (hg₂ : CMDiffAt m g₂ x₀)
    (hmn : m + 1 ≤ n) :
    CMDiffAt m (fun x ↦ inTangentCoordinates I I' g (fun x ↦ f x (g x))
      (fun x ↦ mfderiv% (f x) (g x)) (g₁ x₀) (g₁ x) (g₂ x)) x₀ :=
  ((hf.mfderiv f g hg hmn).comp_of_eq hg₁ rfl).clm_apply hg₂

end mfderiv

/-! ### The tangent map of a `C^(n+1)` function is `C^n` -/

section tangentMap

variable [Is : IsManifold I 1 M] [I's : IsManifold I' 1 M']

theorem ContMDiffOn.contMDiffOn_tangentMapWithin
    (hf : CMDiff[s] n f) (hmn : m + 1 ≤ n) (hs : UniqueMDiffOn I s) :
    CMDiff[(π E (TangentSpace I) ⁻¹' s)] m (tangentMapWithin I I' f s) := by
  intro x₀ hx₀
  let s' : Set (TangentBundle I M) := (π E (TangentSpace I) ⁻¹' s)
  let b₁ : TangentBundle I M → M := fun p ↦ p.1
  let v : Π (y : TangentBundle I M), TangentSpace I (b₁ y) := fun y ↦ y.2
  have hv : ContMDiffWithinAt I.tangent I.tangent m (fun y ↦ (v y : TangentBundle I M)) s' x₀ :=
    contMDiffWithinAt_id
  let b₂ : TangentBundle I M → M' := f ∘ b₁
  have hb₂ : CMDiffAt[s'] m b₂ x₀ :=
    ((hf (b₁ x₀) hx₀).of_le (le_self_add.trans hmn)).comp _
      (contMDiffWithinAt_proj (TangentSpace I)) (fun x h ↦ h)
  let ϕ : Π (y : TangentBundle I M), TangentSpace I (b₁ y) →L[𝕜] TangentSpace I' (b₂ y) :=
    fun y ↦ mfderiv[s] f (b₁ y)
  have hϕ : CMDiffAt[s'] m (fun y ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M)) E'
      (TangentSpace I' (M := M')) (b₁ x₀) (b₁ y) (b₂ x₀) (b₂ y) (ϕ y)) x₀ := by
    have A : CMDiffAt[s] m (fun y ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M)) E'
        (TangentSpace I' (M := M')) (b₁ x₀) y (b₂ x₀) (f y) (mfderiv[s] f y)) (b₁ x₀) :=
      .mfderivWithin_const (hf _ hx₀) hmn hx₀ hs
    exact A.comp _ (contMDiffWithinAt_proj (TangentSpace I)) (fun x h ↦ h)
  exact ContMDiffWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

theorem ContMDiffOn.continuousOn_tangentMapWithin (hf : CMDiff[s] n f) (hmn : 1 ≤ n)
    (hs : UniqueMDiffOn I s) :
    ContinuousOn (tangentMapWithin I I' f s) (π E (TangentSpace I) ⁻¹' s) := by
  have : CMDiff[π E (TangentSpace I) ⁻¹' s] 0 (tangentMapWithin I I' f s) :=
    hf.contMDiffOn_tangentMapWithin hmn hs
  exact this.continuousOn

theorem ContMDiff.contMDiff_tangentMap (hf : CMDiff n f) (hmn : m + 1 ≤ n) :
    CMDiff m (tangentMap I I' f) := by
  rw [← contMDiffOn_univ] at hf ⊢
  convert hf.contMDiffOn_tangentMapWithin hmn uniqueMDiffOn_univ
  rw [tangentMapWithin_univ]

theorem ContMDiff.continuous_tangentMap (hf : CMDiff n f) (hmn : 1 ≤ n) :
    Continuous (tangentMap I I' f) := by
  rw [← contMDiffOn_univ] at hf
  rw [← continuousOn_univ]
  convert hf.continuousOn_tangentMapWithin hmn uniqueMDiffOn_univ
  rw [tangentMapWithin_univ]

end tangentMap

namespace TangentBundle

open Bundle

set_option backward.isDefEq.respectTransparency false in

theorem tangentMap_tangentBundle_pure [Is : IsManifold I 1 M]
    (p : TangentBundle I M) :
    tangentMap I I.tangent (zeroSection E (TangentSpace I)) p = ⟨⟨p.proj, 0⟩, ⟨p.2, 0⟩⟩ := by
  rcases p with ⟨x, v⟩
  have N : I.symm ⁻¹' (chartAt H x).target ∈ 𝓝 (I ((chartAt H x) x)) := by
    apply IsOpen.mem_nhds
    · apply (OpenPartialHomeomorph.open_target _).preimage I.continuous_invFun
    · simp only [mfld_simps]
  have A : MDiffAt (fun x ↦ TotalSpace.mk' E (x : M) (0 : TangentSpace I x)) x :=
    haveI : CMDiff 1 (zeroSection E (TangentSpace I : M → Type _)) :=
      Bundle.contMDiff_zeroSection 𝕜 (TangentSpace I : M → Type _)
    this.mdifferentiableAt one_ne_zero
  have B : fderivWithin 𝕜 (fun x' : E ↦ (x', (0 : E))) (Set.range I) (I ((chartAt H x) x)) v
      = (v, 0) := by
    rw [fderivWithin_eq_fderiv, DifferentiableAt.fderiv_prodMk]
    · simp
    · exact differentiableAt_fun_id
    · exact differentiableAt_const _
    · exact ModelWithCorners.uniqueDiffWithinAt_image I
    · exact differentiableAt_id.prodMk (differentiableAt_const _)
  simp +unfoldPartialApp only [Bundle.zeroSection, tangentMap, mfderiv, A,
    if_pos, chartAt, FiberBundle.chartedSpace_chartAt, TangentBundle.trivializationAt_apply,
    Function.comp_def, map_zero, mfld_simps]
  rw [← fderivWithin_inter N] at B
  rw [← fderivWithin_inter N, ← B]
  congr 1
  refine fderivWithin_congr (fun y hy ↦ ?_) ?_
  · simp only [mfld_simps] at hy
    simp only [hy, mfld_simps]
  · simp only [mfld_simps]

end TangentBundle

namespace ContMDiffMap

open scoped Manifold ContDiff

-- DISSOLVED: mdifferentiable'

protected theorem mdifferentiable (f : C^∞⟮I, M; I', M'⟯) : MDiff f :=
  f.mdifferentiable' (by simp)

protected theorem mdifferentiableAt (f : C^∞⟮I, M; I', M'⟯) {x} : MDiffAt f x :=
  f.mdifferentiable x

end ContMDiffMap

section EquivTangentBundleProd

variable (I I' M M') in
