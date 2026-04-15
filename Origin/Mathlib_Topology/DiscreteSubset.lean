/-
Extracted from Topology/DiscreteSubset.lean
Genuine: 15 of 15 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Discrete subsets of topological spaces

This file contains various additional properties of discrete subsets of topological spaces.

## Discreteness and compact sets

Given a topological space `X` together with a subset `s ⊆ X`, there are two distinct concepts of
"discreteness" which may hold. These are:
  (i) Every point of `s` is isolated (i.e., the subset topology induced on `s` is the discrete
      topology).
 (ii) Every compact subset of `X` meets `s` only finitely often (i.e., the inclusion map `s → X`
      tends to the cocompact filter along the cofinite filter on `s`).

When `s` is closed, the two conditions are equivalent provided `X` is locally compact and T1,
see `IsClosed.tendsto_coe_cofinite_iff`.

### Main statements

* `tendsto_cofinite_cocompact_iff`:
* `IsClosed.tendsto_coe_cofinite_iff`:

## Co-discrete open sets

We define the filter `Filter.codiscreteWithin S`, which is the supremum of all `𝓝[S \ {x}] x`.
This is the filter of all open codiscrete sets within S. We also define `Filter.codiscrete` as
`Filter.codiscreteWithin univ`, which is the filter of all open codiscrete sets in the space.

-/

open Set Filter Function Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {s : Set X}

theorem discreteTopology_subtype_iff {S : Set Y} :
    DiscreteTopology S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ := by
  simp_rw [discreteTopology_iff_nhds_ne, SetCoe.forall', nhds_ne_subtype_eq_bot_iff]

theorem isDiscrete_iff_nhdsNE {S : Set Y} :
    IsDiscrete S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ := by
  rw [isDiscrete_iff_discreteTopology, discreteTopology_subtype_iff]

lemma discreteTopology_of_noAccPts {X : Type*} [TopologicalSpace X] {E : Set X}
    (h : ∀ x ∈ E, ¬ AccPt x (𝓟 E)) : DiscreteTopology E := by
  simpa [discreteTopology_subtype_iff, AccPt] using h

lemma discreteTopology_subtype_iff' {S : Set Y} :
    DiscreteTopology S ↔ ∀ y ∈ S, ∃ U : Set Y, IsOpen U ∧ U ∩ S = {y} := by
  simp [discreteTopology_iff_isOpen_singleton, isOpen_induced_iff, Set.ext_iff]
  grind

theorem isDiscrete_iff_forall_exists_isOpen {S : Set Y} :
    IsDiscrete S ↔ ∀ y ∈ S, ∃ U, IsOpen U ∧ U ∩ S = {y} := by
  rw [isDiscrete_iff_discreteTopology, discreteTopology_subtype_iff']

lemma Set.Subsingleton.isDiscrete (hs : s.Subsingleton) : IsDiscrete s :=
  have : Subsingleton s := (Set.subsingleton_coe s).mpr hs
  ⟨inferInstance⟩

lemma isDiscrete_iff_nhdsWithin : IsDiscrete s ↔ ∀ x ∈ s, 𝓝[s] x = pure x := by
  simp [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure, nhds_induced,
    ← (Filter.map_injective Subtype.val_injective).eq_iff,
    Filter.map_comap, nhdsWithin]

protected alias ⟨IsDiscrete.nhdsWithin, _⟩ := isDiscrete_iff_nhdsWithin

lemma IsDiscrete.of_nhdsWithin (H : ∀ x ∈ s, 𝓝[s] x ≤ pure x) : IsDiscrete s :=
  isDiscrete_iff_nhdsWithin.mpr fun x hx ↦ (H x hx).antisymm (pure_le_nhdsWithin hx)

lemma isDiscrete_univ_iff : IsDiscrete (Set.univ : Set X) ↔ DiscreteTopology X := by
  simp [isDiscrete_iff_nhdsWithin, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure]

lemma IsDiscrete.univ [DiscreteTopology X] : IsDiscrete (Set.univ : Set X) := by
  rwa [isDiscrete_univ_iff]

lemma IsDiscrete.image_of_isOpenMap (hs : IsDiscrete s) (hf : IsOpenMap f)
    (hf' : Function.Injective f) : IsDiscrete (f '' s) := by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pure, ← hs.nhdsWithin x hx, nhdsWithin, nhdsWithin, map_inf hf', map_principal]
  grw [hf.nhds_le x]

lemma IsDiscrete.image_of_isOpenMap_of_isOpen (hs : IsDiscrete s) (hf : IsOpenMap f)
    (hs' : IsOpen s) : IsDiscrete (f '' s) := by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [(hf _ hs').nhdsWithin_eq ⟨x, hx, rfl⟩, ← map_pure, ← hs.nhdsWithin x hx, hs'.nhdsWithin_eq hx]
  exact hf.nhds_le x

lemma IsOpenMap.isDiscrete_range [DiscreteTopology X] (hf : IsOpenMap f) :
    IsDiscrete (Set.range f) := by
  simpa using IsDiscrete.univ.image_of_isOpenMap_of_isOpen hf isOpen_univ

lemma IsDiscrete.image (hs : IsDiscrete s) (hf : IsInducing f) : IsDiscrete (f '' s) := by
  simp_all [isDiscrete_iff_nhdsWithin, ← hf.map_nhdsWithin_eq s]

lemma IsInducing.isDiscrete_range [DiscreteTopology X] (hf : IsInducing f) :
    IsDiscrete (Set.range f) := by
  simpa using IsDiscrete.univ.image hf
