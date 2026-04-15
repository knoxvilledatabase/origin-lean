/-
Extracted from Topology/Covering/Basic.lean
Genuine: 6 of 16 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Covering Maps

This file defines covering maps.

## Main definitions

* `IsEvenlyCovered f x I`: A point `x` is evenly covered by `f : E → X` with fiber `I` if `I` is
  discrete and there is a homeomorphism `f ⁻¹' U ≃ₜ U × I` for some open set `U` containing `x`
  with `f ⁻¹' U` open, such that the induced map `f ⁻¹' U → U` coincides with `f`.
* `IsCoveringMap f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/

open Bundle Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

def IsEvenlyCovered (x : X) (I : Type*) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ IsOpen (f ⁻¹' U) ∧
    ∃ H : f ⁻¹' U ≃ₜ U × I, ∀ x, (H x).1.1 = f x

namespace IsEvenlyCovered

variable {f} {I : Type*} [TopologicalSpace I]

noncomputable def fiberHomeomorph {x : X} (h : IsEvenlyCovered f x I) : I ≃ₜ f ⁻¹' {x} := by
  choose _ U hxU hU hfU H hH using h
  exact
  { toFun i := ⟨H.symm (⟨x, hxU⟩, i), by simp [← hH]⟩
    invFun e := (H ⟨e, by rwa [Set.mem_preimage, (e.2 : f e = x)]⟩).2
    left_inv _ := by simp
    right_inv e := Set.inclusion_injective (Set.preimage_mono (Set.singleton_subset_iff.mpr hxU)) <|
      H.injective <| Prod.ext (Subtype.ext <| by simpa [hH] using e.2.symm) (by simp)
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

noncomputable def toTrivialization' {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    Trivialization I f := by
  choose _ U hxU hU hfU H hH using h
  classical exact
  { toFun e := if he : f e ∈ U then ⟨(H ⟨e, he⟩).1, (H ⟨e, he⟩).2⟩ else ⟨x, Classical.arbitrary I⟩
    invFun xi := H.symm (if hx : xi.1 ∈ U then ⟨xi.1, hx⟩ else ⟨x, hxU⟩, xi.2)
    source := f ⁻¹' U
    target := U ×ˢ Set.univ
    map_source' e (he : f e ∈ U) := by simp [he]
    map_target' _ _ := Subtype.coe_prop _
    left_inv' e (he : f e ∈ U) := by simp [he]
    right_inv' xi := by rintro ⟨hx, -⟩; simpa [hx] using fun h ↦ (h (H.symm _).2).elim
    open_source := hfU
    open_target := hU.prod isOpen_univ
    continuousOn_toFun := continuousOn_iff_continuous_restrict.mpr <|
      ((continuous_subtype_val.prodMap continuous_id).comp H.continuous).congr
      fun ⟨e, (he : f e ∈ U)⟩ ↦ by simp [Prod.map, he]
    continuousOn_invFun := continuousOn_iff_continuous_restrict.mpr <|
      ((continuous_subtype_val.comp H.symm.continuous).comp (by fun_prop :
        Continuous fun ui ↦ ⟨⟨_, ui.2.1⟩, ui.1.2⟩)).congr fun ⟨⟨x, i⟩, ⟨hx, _⟩⟩ ↦ by simp [hx]
    baseSet := U
    open_baseSet := hU
    source_eq := rfl
    target_eq := rfl
    proj_toFun e (he : f e ∈ U) := by simp [he, hH] }

noncomputable def toTrivialization {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    Trivialization (f ⁻¹' {x}) f :=
  h.toTrivialization'.transFiberHomeomorph h.fiberHomeomorph

theorem of_trivialization [DiscreteTopology I] {x : X} {t : Trivialization I f}
    (hx : x ∈ t.baseSet) : IsEvenlyCovered f x I :=
  ⟨‹_›, _, hx, t.open_baseSet, t.source_eq ▸ t.open_source,
  { toFun e := ⟨⟨f e, e.2⟩, (t e).2⟩
    invFun xi := ⟨t.invFun (xi.1, xi.2), by
      rw [Set.mem_preimage, ← t.mem_source]; exact t.map_target (t.target_eq ▸ ⟨xi.1.2, ⟨⟩⟩)⟩
    left_inv e := Subtype.ext <| t.symm_apply_mk_proj (t.mem_source.mpr e.2)
    right_inv xi := by simp [t.proj_symm_apply', t.apply_symm_apply']
    continuous_toFun := (IsInducing.subtypeVal.prodMap .id).continuous_iff.mpr <|
      (continuousOn_iff_continuous_restrict.mp <| t.continuousOn_toFun.mono t.source_eq.ge).congr
      fun e ↦ by simp [t.mk_proj_snd' e.2]
    continuous_invFun := IsInducing.subtypeVal.continuous_iff.mpr <|
      t.continuousOn_invFun.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      fun ⟨x, _⟩ ↦ t.target_eq ▸ ⟨x.2, ⟨⟩⟩ }, fun _ ↦ by simp⟩

variable (I) in

theorem of_preimage_eq_empty [IsEmpty I] {x : X} {U : Set X} (hUx : U ∈ 𝓝 x) (hfU : f ⁻¹' U = ∅) :
    IsEvenlyCovered f x I :=
  have ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hUx
  have hfV : f ⁻¹' V = ∅ := Set.eq_empty_of_subset_empty ((Set.preimage_mono hVU).trans hfU.le)
  have := Set.isEmpty_coe_sort.mpr hfV
  ⟨inferInstance, _, hxV, hV, hfV ▸ isOpen_empty, .empty, isEmptyElim⟩
