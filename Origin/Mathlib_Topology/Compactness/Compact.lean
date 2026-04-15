/-
Extracted from Topology/Compactness/Compact.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Compact sets and compact spaces

## Main results

* `isCompact_univ_pi`: **Tychonov's theorem** - an arbitrary product of compact sets
  is compact.

* `isCompact_generateFrom`: **Alexander's subbasis theorem** - suppose `X` is a topological space
  with a subbasis `S` and `s` is a subset of `X`, then `s` is compact if for any open cover of `s`
  with all elements taken from `S`, there is a finite subcover.
-/

open Set Filter Topology TopologicalSpace Function

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X} {f : X → Y}

section Compact

lemma IsCompact.exists_clusterPt (hs : IsCompact s) {f : Filter X} [NeBot f] (hf : f ≤ 𝓟 s) :
    ∃ x ∈ s, ClusterPt x f := hs hf

lemma IsCompact.exists_mapClusterPt {ι : Type*} (hs : IsCompact s) {f : Filter ι} [NeBot f]
    {u : ι → X} (hf : Filter.map u f ≤ 𝓟 s) :
    ∃ x ∈ s, MapClusterPt x f u := hs hf

lemma IsCompact.exists_clusterPt_of_frequently {l : Filter X} (hs : IsCompact s)
    (hl : ∃ᶠ x in l, x ∈ s) : ∃ a ∈ s, ClusterPt a l :=
  let ⟨a, has, ha⟩ := @hs _ (frequently_mem_iff_neBot.mp hl) inf_le_right
  ⟨a, has, ha.mono inf_le_left⟩

lemma IsCompact.exists_mapClusterPt_of_frequently {l : Filter ι} {f : ι → X} (hs : IsCompact s)
    (hf : ∃ᶠ x in l, f x ∈ s) : ∃ a ∈ s, MapClusterPt a l f :=
  hs.exists_clusterPt_of_frequently hf

theorem IsCompact.compl_mem_sets (hs : IsCompact s) {f : Filter X} (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) :
    sᶜ ∈ f := by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact @hs _ hf inf_le_right

theorem IsCompact.compl_mem_sets_of_nhdsWithin (hs : IsCompact s) {f : Filter X}
    (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine hs.compl_mem_sets fun x hx => ?_
  rcases hf x hx with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  rintro x ⟨h₁, h₂⟩ hs
  exact h₂ (h₁ hs)
