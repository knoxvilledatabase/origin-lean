/-
Extracted from Geometry/Manifold/Immersion.lean
Genuine: 29 of 31 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-! # Smooth immersions

In this file, we define `C^n` immersions between `C^n` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition (concerning the `mfderiv` being injective): future pull requests will
prove that our definition implies the latter, and that both are equivalent for finite-dimensional
manifolds.

This definition can be conveniently formulated in terms of local properties: `f` is an immersion at
`x` iff there exist suitable charts near `x` and `f x` such that `f` has a nice form w.r.t. these
charts. Most results below can be deduced from more abstract results about such local properties.
This shortens the overall argument, as the definition of submersions has the same general form.

## Main definitions

* `IsImmersionAtOfComplement F I J n f x` means a map `f : M → N` between `C^n` manifolds `M` and
  `N` is an immersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`, w.r.t. some equivalence
  `E' ≃L[𝕜] E × F`. We do not demand that `f` be differentiable (this follows from this definition).
* `IsImmersionAt I J n f x` means that `f` is a `C^n` immersion at `x : M` for some choice of a
  complement `F` of the model normed space `E` of `M` in the model normed space `E'` of `N`.
  In most cases, prefer this definition over `IsImmersionAtOfComplement`.
* `IsImmersionOfComplement F I J n f` means `f : M → N` is an immersion at every point `x : M`,
  w.r.t. the chosen complement `F`.
* `IsImmersion I J n f` means `f : M → N` is an immersion at every point `x : M`,
  w.r.t. some global choice of complement.

## Main results

* `IsImmersionAt.congr_of_eventuallyEq`: being an immersion is a local property.
  If `f` and `g` agree near `x` and `f` is an immersion at `x`, so is `g`
* `IsImmersionAtOfComplement.congr_F`, `IsImmersionOfComplement.congr_F`:
  being an immersion (at `x`) w.r.t. `F` is stable under
  replacing the complement `F` by an isomorphic copy
* `IsOpen.isImmersionAtOfComplement` and `IsOpen.isImmersionAt`:
  the set of points where `IsImmersionAt(OfComplement)` holds is open.
* `IsImmersionAt.prodMap` and `IsImmersion.prodMap`: the product of two immersions (at a point)
  is an immersion (at a point).
* `IsImmersion.id`: the identity map is an immersion
* `IsImmersion.of_opens`: the inclusion of an open subset `s → M` of a smooth manifold
  is a smooth immersion

## Implementation notes

* In most applications, there is no need to control the chosen complement in the definition of
  immersions, so `IsImmersion(At)` is perfectly fine to use. Such control will be helpful, however,
  when considering the local characterisation of submanifolds: locally, a submanifold is described
  either as the image of an immersion, or the preimage of a submersion --- w.r.t. the same
  complement. Having access to a definition version with complements allows stating this equivalence
  cleanly.
* To avoid a free universe variable in `IsImmersion(At)`, we ask for a complement in the same
  universe as the model normed space for `N`. We provide convenience constructors which do not
  have this restriction (recovering usability).
  The underlying observation is that the equivalence in the definition of immersions allows
  shrinking the universe of the complement: this is implemented in
  `IsImmersion(At)OfComplement.small` and `IsImmersion(At)OfComplement.smallEquiv`.

## TODO
* The converse to `IsImmersionAtOfComplement.congr_F` also holds: any two complements are
  isomorphic, as they are isomorphic to the cokernel of the differential `mfderiv I J f x`.
* `IsImmersionAt.contMDiffAt`: if f is an immersion at `x`, it is `C^n` at `x`.
* `IsImmersion.contMDiff`: if f is an immersion, it is `C^n`.
* If `f` is an immersion at `x`, its differential splits, hence is injective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` splitting implies `f` is an
  immersion at `x`. (This requires the inverse function theorem.)
* `IsImmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is an immersion at `x : M` and `g` is an immersion at `f x`, then `g ∘ f` is an immersion
  at `x`.
* `IsImmersion.comp`: the composition of immersions (between Banach manifolds) is an immersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being injective
  implies `f` is an immersion at `x`.
* `IsLocalDiffeomorphAt.isImmersionAt` and `IsLocalDiffeomorph.isImmersion`:
  a local diffeomorphism (at `x`) is an immersion (at `x`)
* `Diffeomorph.isImmersion`: in particular, a diffeomorphism is an immersion

## References

* [Juan Margalef-Roig and Enrique Outerelo Dominguez, *Differential topology*][roigdomingues1992]

-/

open scoped Topology ContDiff

open Function Set Manifold

noncomputable section

namespace Manifold

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E''' : Type*} {E'' : Type u} {F F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

variable (F I J M N) in

def ImmersionAtProp : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop :=
  fun f domChart codChart ↦ ∃ equiv : (E × F) ≃L[𝕜] E'',
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in

lemma isLocalSourceTargetProperty_immersionAtProp :
    IsLocalSourceTargetProperty (ImmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs hf := by
    obtain ⟨equiv, hf⟩ := hf
    exact ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg hf := by
    obtain ⟨equiv, hf⟩ := hf
    refine ⟨equiv, EqOn.trans (fun x hx ↦ ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x ∈ φ.source := by simp_all
    grind

variable (F I J n) in

irreducible_def IsImmersionAtOfComplement (f : M → N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N)

variable (I J n) in

irreducible_def IsImmersionAt (f : M → N) (x : M) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsImmersionAtOfComplement F I J n f x

variable {f g : M → N} {x : M}

namespace IsImmersionAtOfComplement

lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H)
    (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x := by
  rw [IsImmersionAtOfComplement_def]
  use domChart, codChart
  use equiv

lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x := by
  rw [IsImmersionAtOfComplement_def]
  exact LiftSourceTargetPropertyAt.mk_of_continuousAt hf isLocalSourceTargetProperty_immersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

def domChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph M H := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.domChart h

def codChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph N G := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.codChart h

lemma mem_domChart_source (h : IsImmersionAtOfComplement F I J n f x) : x ∈ h.domChart.source := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.mem_domChart_source h

lemma mem_codChart_source (h : IsImmersionAtOfComplement F I J n f x) :
    f x ∈ h.codChart.source := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.mem_codChart_source h

lemma domChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h

lemma codChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h

lemma source_subset_preimage_source (h : IsImmersionAtOfComplement F I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source := by
  rw [IsImmersionAtOfComplement_def] at h
  exact LiftSourceTargetPropertyAt.source_subset_preimage_source h

def equiv (h : IsImmersionAtOfComplement F I J n f x) : (E × F) ≃L[𝕜] E'' := by
  rw [IsImmersionAtOfComplement_def] at h
  exact Classical.choose <| LiftSourceTargetPropertyAt.property h

lemma writtenInCharts (h : IsImmersionAtOfComplement F I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target := by
  rw [IsImmersionAtOfComplement_def] at h
  exact Classical.choose_spec <| LiftSourceTargetPropertyAt.property h

lemma property (h : IsImmersionAtOfComplement F I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N) := by
  rwa [IsImmersionAtOfComplement_def] at h

lemma map_target_subset_target (h : IsImmersionAtOfComplement F I J n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target := by
  rw [← h.writtenInCharts.image_eq, Set.image_comp, Set.image_comp,
    PartialEquiv.symm_image_target_eq_source, OpenPartialHomeomorph.extend_source,
    ← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source ⊆ h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

lemma target_subset_preimage_target (h : IsImmersionAtOfComplement F I J n f x) :
    (h.domChart.extend I).target ⊆ (h.equiv ∘ (·, 0)) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx ↦ h.map_target_subset_target (mem_image_of_mem _ hx)

lemma congr_of_eventuallyEq (hf : IsImmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n g x := by
  rw [IsImmersionAtOfComplement_def]
  exact LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_immersionAtProp hf.property hfg

lemma congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F I J n g x := by
  simpa only [IsImmersionAtOfComplement_def] using
    LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
      isLocalSourceTargetProperty_immersionAtProp hfg

lemma small (hf : IsImmersionAtOfComplement F I J n f x) : Small.{u} F :=
  small_of_injective <| hf.equiv.injective.comp (Prod.mk_right_injective 0)

def smallComplement (hf : IsImmersionAtOfComplement F I J n f x) : Type u :=
  haveI := hf.small
  Shrink.{u} F

-- INSTANCE (free from Core): (hf

-- INSTANCE (free from Core): (hf

def smallEquiv (hf : IsImmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement :=
  haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm

lemma trans_F (h : IsImmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F' I J n f x := by
  rewrite [IsImmersionAtOfComplement_def]
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr e.symm).trans h.equiv
  apply Set.EqOn.trans h.writtenInCharts
  intro x hx
  simp

lemma congr_F (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F' I J n f x :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

lemma _root_.IsOpen.isImmersionAtOfComplement :
    IsOpen {x | IsImmersionAtOfComplement F I J n f x} := by
  simp_rw [IsImmersionAtOfComplement_def]
  exact .liftSourceTargetPropertyAt

set_option backward.isDefEq.respectTransparency false in

theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersionAtOfComplement F I J n f x) (hg : IsImmersionAtOfComplement F' I' J' n g x') :
    IsImmersionAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  rw [IsImmersionAtOfComplement_def]
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' F F').trans (equiv₁.prodCongr equiv₂)
  rw [φ₁.extend_prod φ₂, ψ₁.extend_prod, PartialEquiv.prod_target, eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ ↦ by simpa using hfprop hx, fun x ⟨hx, hx'⟩ ↦ by simpa using hgprop hx'⟩

lemma isImmersionAt (h : IsImmersionAtOfComplement F I J n f x) :
    IsImmersionAt I J n f x := by
  rw [IsImmersionAt_def]
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionAtOfComplement.congr_F h.smallEquiv).mp h

open IsManifold in

lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (y : s) :
    IsImmersionAtOfComplement PUnit I I n (Subtype.val : s → M) y := by
  apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) (.prodUnique 𝕜 E _)
    (chartAt H y) (chartAt H y.val) (mem_chart_source H y) (mem_chart_source H y.val)
    (chart_mem_maximalAtlas y) (chart_mem_maximalAtlas y.val)
  intro x hx
  suffices I ((chartAt H ↑y) ((chartAt H y).symm (I.symm x))) = x by simpa +contextual
  simp_all
