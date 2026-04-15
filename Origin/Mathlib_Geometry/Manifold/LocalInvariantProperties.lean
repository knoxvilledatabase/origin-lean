/-
Extracted from Geometry/Manifold/LocalInvariantProperties.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Local properties invariant under a groupoid

We study properties of a triple `(g, s, x)` where `g` is a function between two spaces `H` and `H'`,
`s` is a subset of `H` and `x` is a point of `H`. Our goal is to register how such a property
should behave to make sense in charted spaces modelled on `H` and `H'`.

The main examples we have in mind are the properties "`g` is differentiable at `x` within `s`", or
"`g` is smooth at `x` within `s`". We want to develop general results that, when applied in these
specific situations, say that the notion of smooth function in a manifold behaves well under
restriction, intersection, is local, and so on.

## Main definitions

* `LocalInvariantProp G G' P` says that a property `P` of a triple `(g, s, x)` is local, and
  invariant under composition by elements of the groupoids `G` and `G'` of `H` and `H'`
  respectively.
* `ChartedSpace.LiftPropWithinAt` (resp. `LiftPropAt`, `LiftPropOn` and `LiftProp`):
  given a property `P` of `(g, s, x)` where `g : H → H'`, define the corresponding property
  for functions `M → M'` where `M` and `M'` are charted spaces modelled respectively on `H` and
  `H'`. We define these properties within a set at a point, or at a point, or on a set, or in the
  whole space. This lifting process (obtained by restricting to suitable chart domains) can always
  be done, but it only behaves well under locality and invariance assumptions.

Given `hG : LocalInvariantProp G G' P`, we deduce many properties of the lifted property on the
charted spaces. For instance, `hG.liftPropWithinAt_inter` says that `P g s x` is equivalent to
`P g (s ∩ t) x` whenever `t` is a neighborhood of `x`.

## Implementation notes

We do not use dot notation for properties of the lifted property. For instance, we have
`hG.liftPropWithinAt_congr` saying that if `LiftPropWithinAt P g s x` holds, and `g` and `g'`
coincide on `s`, then `LiftPropWithinAt P g' s x` holds. We can't call it
`LiftPropWithinAt.congr` as it is in the namespace associated to `LocalInvariantProp`, not
in the one for `LiftPropWithinAt`.
-/

noncomputable section

open Set Filter TopologicalSpace

open scoped Manifold Topology

variable {H M H' M' X : Type*}

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

variable [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']

variable [TopologicalSpace X]

namespace StructureGroupoid

variable (G : StructureGroupoid H) (G' : StructureGroupoid H')

structure LocalInvariantProp (P : (H → H') → Set H → H → Prop) : Prop where
  is_local : ∀ {s x u} {f : H → H'}, IsOpen u → x ∈ u → (P f s x ↔ P f (s ∩ u) x)
  right_invariance' : ∀ {s x f} {e : OpenPartialHomeomorph H H},
    e ∈ G → x ∈ e.source → P f s x → P (f ∘ e.symm) (e.symm ⁻¹' s) (e x)
  congr_of_forall : ∀ {s x} {f g : H → H'}, (∀ y ∈ s, f y = g y) → f x = g x → P f s x → P g s x
  left_invariance' : ∀ {s x f} {e' : OpenPartialHomeomorph H' H'},
    e' ∈ G' → s ⊆ f ⁻¹' e'.source → f x ∈ e'.source → P f s x → P (e' ∘ f) s x

variable {G G'} {P : (H → H') → Set H → H → Prop}

variable (hG : G.LocalInvariantProp G' P)

include hG

namespace LocalInvariantProp

theorem congr_set {s t : Set H} {x : H} {f : H → H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x := by
  obtain ⟨o, host, ho, hxo⟩ := mem_nhds_iff.mp hu.mem_iff
  simp_rw [subset_def, mem_setOf, ← and_congr_left_iff, ← mem_inter_iff, ← Set.ext_iff] at host
  rw [hG.is_local ho hxo, host, ← hG.is_local ho hxo]

theorem is_local_nhds {s u : Set H} {x : H} {f : H → H'} (hu : u ∈ 𝓝[s] x) :
    P f s x ↔ P f (s ∩ u) x :=
  hG.congr_set <| mem_nhdsWithin_iff_eventuallyEq.mp hu

theorem congr_iff_nhdsWithin {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g)
    (h2 : f x = g x) : P f s x ↔ P g s x := by
  simp_rw [hG.is_local_nhds h1]
  exact ⟨hG.congr_of_forall (fun y hy ↦ hy.2) h2, hG.congr_of_forall (fun y hy ↦ hy.2.symm) h2.symm⟩

theorem congr_nhdsWithin {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
    (hP : P f s x) : P g s x :=
  (hG.congr_iff_nhdsWithin h1 h2).mp hP

theorem congr_nhdsWithin' {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
    (hP : P g s x) : P f s x :=
  (hG.congr_iff_nhdsWithin h1 h2).mpr hP

theorem congr_iff {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x :=
  hG.congr_iff_nhdsWithin (mem_nhdsWithin_of_mem_nhds h) (mem_of_mem_nhds h :)

theorem congr {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x) : P g s x :=
  (hG.congr_iff h).mp hP

theorem congr' {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x) : P f s x :=
  hG.congr h.symm hP

theorem left_invariance {s : Set H} {x : H} {f : H → H'} {e' : OpenPartialHomeomorph H' H'}
    (he' : e' ∈ G') (hfs : ContinuousWithinAt f s x) (hxe' : f x ∈ e'.source) :
    P (e' ∘ f) s x ↔ P f s x := by
  have h2f := hfs.preimage_mem_nhdsWithin (e'.open_source.mem_nhds hxe')
  have h3f :=
    ((e'.continuousAt hxe').comp_continuousWithinAt hfs).preimage_mem_nhdsWithin <|
      e'.symm.open_source.mem_nhds <| e'.mapsTo hxe'
  constructor
  · intro h
    rw [hG.is_local_nhds h3f] at h
    have h2 := hG.left_invariance' (G'.symm he') inter_subset_right (e'.mapsTo hxe') h
    rw [← hG.is_local_nhds h3f] at h2
    refine hG.congr_nhdsWithin ?_ (e'.left_inv hxe') h2
    exact eventually_of_mem h2f fun x' ↦ e'.left_inv
  · simp_rw [hG.is_local_nhds h2f]
    exact hG.left_invariance' he' inter_subset_right hxe'

theorem right_invariance {s : Set H} {x : H} {f : H → H'} {e : OpenPartialHomeomorph H H}
    (he : e ∈ G) (hxe : x ∈ e.source) : P (f ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P f s x := by
  refine ⟨fun h ↦ ?_, hG.right_invariance' he hxe⟩
  have := hG.right_invariance' (G.symm he) (e.mapsTo hxe) h
  rw [e.symm_symm, e.left_inv hxe] at this
  refine hG.congr ?_ ((hG.congr_set ?_).mp this)
  · refine eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' ↦ ?_
    simp_rw [Function.comp_apply, e.left_inv hx']
  · rw [eventuallyEq_set]
    refine eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' ↦ ?_
    simp_rw [mem_preimage, e.left_inv hx']

end LocalInvariantProp

end StructureGroupoid

namespace ChartedSpace
