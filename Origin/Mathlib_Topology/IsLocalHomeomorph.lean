/-
Extracted from Topology/IsLocalHomeomorph.lean
Genuine: 30 of 34 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Local homeomorphisms

This file defines local homeomorphisms.

## Main definitions

For a function `f : X → Y ` between topological spaces, we say
* `IsLocalHomeomorphOn f s` if `f` is a local homeomorphism around each point of `s`: for each
  `x : X`, the restriction of `f` to some open neighborhood `U` of `x` gives a homeomorphism
  between `U` and an open subset of `Y`.
* `IsLocalHomeomorph f`: `f` is a local homeomorphism, i.e. it's a local homeomorphism on `univ`.

Note that `IsLocalHomeomorph` is a global condition. This is in contrast to
`OpenPartialHomeomorph`, which is a homeomorphism between specific open subsets.

## Main results
* local homeomorphisms are locally injective open maps
* more!

-/

open Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  (f : X → Y) (s : Set X) (t : Set Y)

def IsLocalHomeomorphOn :=
  ∀ x ∈ s, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ f = e

namespace IsLocalHomeomorphOn

variable {f s}

lemma isDiscrete_of_image (h : IsLocalHomeomorphOn f s)
    (hs : IsDiscrete (f '' s)) : IsDiscrete s :=
  have := hs.1; ⟨discreteTopology_of_image h⟩

lemma isDiscrete_image_iff (h : IsLocalHomeomorphOn f s) (hs : IsOpen s) :
    IsDiscrete (f '' s) ↔ IsDiscrete s :=
  ⟨h.isDiscrete_of_image, fun hs' ↦ ⟨h.discreteTopology_image_iff hs |>.mpr hs'.to_subtype⟩⟩

variable (f s) in

lemma OpenPartialHomeomorph.isLocalHomeomorphOn (e : OpenPartialHomeomorph X Y) :
    IsLocalHomeomorphOn e e.source :=
  fun _ hx ↦ ⟨e, hx, rfl⟩

variable {g t}

theorem mono {t : Set X} (hf : IsLocalHomeomorphOn f t) (hst : s ⊆ t) : IsLocalHomeomorphOn f s :=
  fun x hx ↦ hf x (hst hx)

theorem of_comp_left (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hg : IsLocalHomeomorphOn g (f '' s))
    (cont : ∀ x ∈ s, ContinuousAt f x) : IsLocalHomeomorphOn f s := mk f s fun x hx ↦ by
  obtain ⟨g, hxg, rfl⟩ := hg (f x) ⟨x, hx, rfl⟩
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨(gf.restr <| f ⁻¹' g.source).trans g.symm, ⟨⟨hgf, mem_interior_iff_mem_nhds.mpr
    ((cont x hx).preimage_mem_nhds <| g.open_source.mem_nhds hxg)⟩, he ▸ g.map_source hxg⟩,
    fun y hy ↦ ?_⟩
  change f y = g.symm (gf y)
  have : f y ∈ g.source := by apply interior_subset hy.1.2
  rw [← he, g.eq_symm_apply this (by apply g.map_source this), Function.comp_apply]

theorem of_comp_right (hgf : IsLocalHomeomorphOn (g ∘ f) s) (hf : IsLocalHomeomorphOn f s) :
    IsLocalHomeomorphOn g (f '' s) := mk g _ <| by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨f, hxf, rfl⟩ := hf x hx
  obtain ⟨gf, hgf, he⟩ := hgf x hx
  refine ⟨f.symm.trans gf, ⟨f.map_source hxf, ?_⟩, fun y hy ↦ ?_⟩
  · apply (f.left_inv hxf).symm ▸ hgf
  · change g y = gf (f.symm y)
    rw [← he, Function.comp_apply, f.right_inv hy.1]

theorem map_nhds_eq (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x ∈ s) : (𝓝 x).map f = 𝓝 (f x) :=
  let ⟨e, hx, he⟩ := hf x hx
  he.symm ▸ e.map_nhds_eq hx

protected theorem continuousAt (hf : IsLocalHomeomorphOn f s) {x : X} (hx : x ∈ s) :
    ContinuousAt f x :=
  (hf.map_nhds_eq hx).le

protected theorem continuousOn (hf : IsLocalHomeomorphOn f s) : ContinuousOn f s :=
  continuousOn_of_forall_continuousAt fun _x ↦ hf.continuousAt

protected theorem comp (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩

end IsLocalHomeomorphOn

def IsLocalHomeomorph :=
  ∀ x : X, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ f = e

theorem Homeomorph.isLocalHomeomorph (f : X ≃ₜ Y) : IsLocalHomeomorph f :=
  fun _ ↦ ⟨f.toOpenPartialHomeomorph, trivial, rfl⟩

variable {f s}

theorem isLocalHomeomorph_iff_isLocalHomeomorphOn_univ :
    IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ :=
  ⟨fun h x _ ↦ h x, fun h x ↦ h x trivial⟩

protected theorem IsLocalHomeomorph.isLocalHomeomorphOn (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorphOn f s := fun x _ ↦ hf x

theorem isLocalHomeomorph_iff_isOpenEmbedding_restrict {f : X → Y} :
    IsLocalHomeomorph f ↔ ∀ x : X, ∃ U ∈ 𝓝 x, IsOpenEmbedding (U.restrict f) := by
  simp_rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ,
    isLocalHomeomorphOn_iff_isOpenEmbedding_restrict, imp_iff_right (Set.mem_univ _)]

theorem Topology.IsOpenEmbedding.isLocalHomeomorph (hf : IsOpenEmbedding f) : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun _ ↦
    ⟨_, Filter.univ_mem, hf.comp (Homeomorph.Set.univ X).isOpenEmbedding⟩

namespace IsLocalHomeomorph

theorem comap_discreteTopology (h : IsLocalHomeomorph f)
    [DiscreteTopology Y] : DiscreteTopology X :=
  (Homeomorph.Set.univ X).discreteTopology_iff.mp h.isLocalHomeomorphOn.discreteTopology_of_image

theorem discreteTopology_range_iff (h : IsLocalHomeomorph f) :
    DiscreteTopology (Set.range f) ↔ DiscreteTopology X := by
  rw [← Set.image_univ, ← (Homeomorph.Set.univ X).discreteTopology_iff]
  exact h.isLocalHomeomorphOn.discreteTopology_image_iff isOpen_univ

theorem discreteTopology_iff_of_surjective (h : IsLocalHomeomorph f) (hs : Function.Surjective f) :
    DiscreteTopology X ↔ DiscreteTopology Y := by
  rw [← (Homeomorph.Set.univ Y).discreteTopology_iff, ← hs.range_eq, h.discreteTopology_range_iff]

variable (f)

theorem mk (h : ∀ x : X, ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ Set.EqOn f e e.source) :
    IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (IsLocalHomeomorphOn.mk f Set.univ fun x _hx ↦ h x)

lemma Homeomorph.isLocalHomeomorph (h : X ≃ₜ Y) : IsLocalHomeomorph h :=
  fun _ ↦ ⟨h.toOpenPartialHomeomorph, trivial, rfl⟩

variable {g f}

lemma isLocallyInjective (hf : IsLocalHomeomorph f) : IsLocallyInjective f :=
  fun x ↦ by obtain ⟨f, hx, rfl⟩ := hf x; exact ⟨f.source, f.open_source, hx, f.injOn⟩

theorem of_comp (hgf : IsLocalHomeomorph (g ∘ f)) (hg : IsLocalHomeomorph g)
    (cont : Continuous f) : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
    hgf.isLocalHomeomorphOn.of_comp_left hg.isLocalHomeomorphOn fun _ _ ↦ cont.continuousAt

theorem map_nhds_eq (hf : IsLocalHomeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) :=
  hf.isLocalHomeomorphOn.map_nhds_eq (Set.mem_univ x)

protected theorem continuous (hf : IsLocalHomeomorph f) : Continuous f :=
  continuousOn_univ.mp hf.isLocalHomeomorphOn.continuousOn

protected theorem isOpenMap (hf : IsLocalHomeomorph f) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun x ↦ ge_of_eq (hf.map_nhds_eq x)

protected theorem comp (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorph (g ∘ f) :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    (hg.isLocalHomeomorphOn.comp hf.isLocalHomeomorphOn (Set.univ.mapsTo_univ f))

theorem isOpenEmbedding_of_injective (hf : IsLocalHomeomorph f) (hi : f.Injective) :
    IsOpenEmbedding f :=
  .of_continuous_injective_isOpenMap hf.continuous hi hf.isOpenMap

noncomputable def toHomeomorphOfBijective (hf : IsLocalHomeomorph f) (hb : f.Bijective) :
    X ≃ₜ Y :=
  (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous hf.isOpenMap
