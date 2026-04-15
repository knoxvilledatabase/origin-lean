/-
Extracted from Topology/CompactOpen.lean
Genuine: 14 of 16 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The compact-open topology

In this file, we define the compact-open topology on the set of continuous maps between two
topological spaces.

## Main definitions

* `ContinuousMap.compactOpen` is the compact-open topology on `C(X, Y)`.
  It is declared as an instance.
* `ContinuousMap.coev` is the coevaluation map `Y → C(X, Y × X)`. It is always continuous.
* `ContinuousMap.curry` is the currying map `C(X × Y, Z) → C(X, C(Y, Z))`. This map always exists
  and it is continuous as long as `X × Y` is locally compact.
* `ContinuousMap.uncurry` is the uncurrying map `C(X, C(Y, Z)) → C(X × Y, Z)`. For this map to
  exist, we need `Y` to be locally compact. If `X` is also locally compact, then this map is
  continuous.
* `Homeomorph.curry` combines the currying and uncurrying operations into a homeomorphism
  `C(X × Y, Z) ≃ₜ C(X, C(Y, Z))`. This homeomorphism exists if `X` and `Y` are locally compact.


## Tags

compact-open, curry, function space
-/

open Set Filter TopologicalSpace Topology

namespace ContinuousMap

section CompactOpen

variable {α X Y Z T : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]

variable {K : Set X} {U : Set Y}

-- INSTANCE (free from Core): compactOpen

theorem isOpen_setOf_mapsTo (hK : IsCompact K) (hU : IsOpen U) :
    IsOpen {f : C(X, Y) | MapsTo f K U} :=
  isOpen_generateFrom_of_mem <| mem_image2_of_mem hK hU

lemma eventually_mapsTo {f : C(X, Y)} (hK : IsCompact K) (hU : IsOpen U) (h : MapsTo f K U) :
    ∀ᶠ g : C(X, Y) in 𝓝 f, MapsTo g K U :=
  (isOpen_setOf_mapsTo hK hU).mem_nhds h

lemma isOpen_setOf_range_subset [CompactSpace X] (hU : IsOpen U) :
    IsOpen {f : C(X, Y) | range f ⊆ U} := by
  simp_rw [← mapsTo_univ_iff_range_subset]
  exact isOpen_setOf_mapsTo isCompact_univ hU

lemma eventually_range_subset [CompactSpace X] {f : C(X, Y)} (hU : IsOpen U) (h : range f ⊆ U) :
    ∀ᶠ g : C(X, Y) in 𝓝 f, range g ⊆ U :=
  (isOpen_setOf_range_subset hU).mem_nhds h

lemma nhds_compactOpen (f : C(X, Y)) :
    𝓝 f = ⨅ (K : Set X) (_ : IsCompact K) (U : Set Y) (_ : IsOpen U) (_ : MapsTo f K U),
      𝓟 {g : C(X, Y) | MapsTo g K U} := by
  simp_rw +instances [compactOpen_eq, nhds_generateFrom, mem_setOf_eq, @and_comm (f ∈ _), iInf_and,
    ← image_prod, iInf_image, biInf_prod, mem_setOf_eq]

lemma tendsto_nhds_compactOpen {l : Filter α} {f : α → C(Y, Z)} {g : C(Y, Z)} :
    Tendsto f l (𝓝 g) ↔
      ∀ K, IsCompact K → ∀ U, IsOpen U → MapsTo g K U → ∀ᶠ a in l, MapsTo (f a) K U := by
  simp [nhds_compactOpen]

lemma continuous_compactOpen {f : X → C(Y, Z)} :
    Continuous f ↔ ∀ K, IsCompact K → ∀ U, IsOpen U → IsOpen {x | MapsTo (f x) K U} :=
  continuous_generateFrom_iff.trans forall_mem_image2

protected lemma hasBasis_nhds (f : C(X, Y)) :
    (𝓝 f).HasBasis
      (fun S : Set (Set X × Set Y) ↦
        S.Finite ∧ ∀ K U, (K, U) ∈ S → IsCompact K ∧ IsOpen U ∧ MapsTo f K U)
      (⋂ KU ∈ ·, {g : C(X, Y) | MapsTo g KU.1 KU.2}) := by
  refine ⟨fun s ↦ ?_⟩
  simp_rw [nhds_compactOpen, iInf_comm.{_, 0, _ + 1}, iInf_prod', iInf_and']
  simp [mem_biInf_principal, and_assoc]

protected lemma mem_nhds_iff {f : C(X, Y)} {s : Set C(X, Y)} :
    s ∈ 𝓝 f ↔ ∃ S : Set (Set X × Set Y), S.Finite ∧
      (∀ K U, (K, U) ∈ S → IsCompact K ∧ IsOpen U ∧ MapsTo f K U) ∧
      {g : C(X, Y) | ∀ K U, (K, U) ∈ S → MapsTo g K U} ⊆ s := by
  simp [f.hasBasis_nhds.mem_iff, ← setOf_forall, and_assoc]

lemma _root_.Filter.HasBasis.nhds_continuousMapConst {ι : Type*} {c : Y} {p : ι → Prop}
    {U : ι → Set Y} (h : (𝓝 c).HasBasis p U) :
    (𝓝 (const X c)).HasBasis (fun Ki : Set X × ι ↦ IsCompact Ki.1 ∧ p Ki.2)
      fun Ki ↦ {f : C(X, Y) | MapsTo f Ki.1 (U Ki.2)} := by
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩⟩
  · rcases ContinuousMap.mem_nhds_iff.mp hs with ⟨S, hSf, hS, hSsub⟩
    choose hScompact hSopen hSmaps using hS
    have : ⋂ KU ∈ S, ⋂ (_ : KU.1.Nonempty), KU.2 ∈ 𝓝 c := by
      simp only [biInter_mem hSf, Prod.forall, iInter_mem]
      rintro K U hKU ⟨x, hx⟩
      exact (hSopen K U hKU).mem_nhds <| hSmaps K U hKU hx
    rcases h.mem_iff.mp this with ⟨i, hpi, hi⟩
    refine ⟨(⋃ KU ∈ S, KU.1, i), ⟨hSf.isCompact_biUnion <| Prod.forall.2 hScompact, hpi⟩,
      Subset.trans ?_ hSsub⟩
    intro f hf K V hKV
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact mapsTo_empty _ _
    · refine hf.out.mono (subset_biUnion_of_mem (u := Prod.fst) hKV) (hi.trans ?_)
      exact (biInter_subset_of_mem hKV).trans <| iInter_subset _ hKne
  · rcases hs with ⟨⟨K, i⟩, ⟨hK, hpi⟩, hi⟩
    filter_upwards [eventually_mapsTo hK isOpen_interior fun x _ ↦
      mem_interior_iff_mem_nhds.mpr <| h.mem_of_mem hpi] with f hf
    exact hi <| hf.mono_right interior_subset

section Functorial

theorem continuous_postcomp (g : C(Y, Z)) : Continuous (ContinuousMap.comp g : C(X, Y) → C(X, Z)) :=
  continuous_compactOpen.2 fun _K hK _U hU ↦ isOpen_setOf_mapsTo hK (hU.preimage g.2)

theorem postcomp_injective (g : C(Y, Z)) (hg : Function.Injective g) :
    Function.Injective (ContinuousMap.comp g : C(X, Y) → C(X, Z)) :=
  fun _ _ ↦ (cancel_left hg).1

theorem isInducing_postcomp (g : C(Y, Z)) (hg : IsInducing g) :
    IsInducing (g.comp : C(X, Y) → C(X, Z)) where
  eq_induced := by
    simp only [compactOpen_eq, induced_generateFrom_eq, image_image2, hg.setOf_isOpen,
      image2_image_right, MapsTo, mem_preimage, preimage_setOf_eq, comp_apply]

theorem isEmbedding_postcomp (g : C(Y, Z)) (hg : IsEmbedding g) :
    IsEmbedding (g.comp : C(X, Y) → C(X, Z)) :=
  ⟨isInducing_postcomp g hg.1, postcomp_injective g hg.2⟩
