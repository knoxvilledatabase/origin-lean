/-
Extracted from Topology/UniformSpace/Completion.lean
Genuine: 23 of 34 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core

/-!
# Hausdorff completions of uniform spaces

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `Completion α` and a morphism
(i.e. uniformly continuous map) `(↑) : α → Completion α` which solves the universal
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`.
It means any uniformly continuous `f : α → β` gives rise to a unique morphism
`Completion.extension f : Completion α → β` such that `f = Completion.extension f ∘ (↑)`.
Actually `Completion.extension f` is defined for all maps from `α` to `β` but it has the desired
properties only if `f` is uniformly continuous.

Beware that `(↑)` is not injective if `α` is not Hausdorff. But its image is always
dense. The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, it turns `f : α → β` into a morphism
  `Completion.map f : Completion α → Completion β`
such that
  `(↑) ∘ f = (Completion.map f) ∘ (↑)`
provided `f` is uniformly continuous. This construction is compatible with composition.

In this file we introduce the following concepts:

* `CauchyFilter α` the uniform completion of the uniform space `α` (using Cauchy filters).
  These are not minimal filters.

* `Completion α := Quotient (separationSetoid (CauchyFilter α))` the Hausdorff completion.

## References

This formalization is mostly based on
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
From a slightly different perspective in order to reuse material in `Topology.UniformSpace.Basic`.
-/

noncomputable section

open Filter Set

open scoped SetRel Uniformity Topology

universe u v w

def CauchyFilter (α : Type u) [UniformSpace α] : Type u :=
  { f : Filter α // Cauchy f }

namespace CauchyFilter

variable {α : Type u} [UniformSpace α]

variable {β : Type v} {γ : Type w}

variable [UniformSpace β] [UniformSpace γ]

-- INSTANCE (free from Core): (f

def gen (s : SetRel α α) : SetRel (CauchyFilter α) (CauchyFilter α) :=
  { p | s ∈ p.1.val ×ˢ p.2.val }

theorem monotone_gen : Monotone (gen : SetRel α α → _) :=
  monotone_setOf fun p => @Filter.monotone_mem _ (p.1.val ×ˢ p.2.val)

set_option backward.privateInPublic true in

private theorem symm_gen : map Prod.swap ((𝓤 α).lift' gen) ≤ (𝓤 α).lift' gen := by
  let f := fun s : SetRel α α =>
        { p : CauchyFilter α × CauchyFilter α | s ∈ (p.2.val ×ˢ p.1.val : Filter (α × α)) }
  have h₁ : map Prod.swap ((𝓤 α).lift' gen) = (𝓤 α).lift' f := by
    delta gen
    simp [f, map_lift'_eq, monotone_setOf, Filter.monotone_mem, Function.comp_def,
      image_swap_eq_preimage_swap]
  have h₂ : (𝓤 α).lift' f ≤ (𝓤 α).lift' gen :=
    uniformity_lift_le_swap
      (monotone_principal.comp
        (monotone_setOf fun p => @Filter.monotone_mem _ (p.2.val ×ˢ p.1.val)))
      (by
        have h := fun p : CauchyFilter α × CauchyFilter α => @Filter.prod_comm _ _ p.2.val p.1.val
        simp only [Function.comp, h, mem_map, f]
        exact le_rfl)
  exact h₁.trans_le h₂

set_option backward.privateInPublic true in

private theorem comp_gen : ((𝓤 α).lift' gen).lift' (fun s ↦ s ○ s) ≤ (𝓤 α).lift' gen :=
  calc
        ((𝓤 α).lift' gen).lift' (fun s ↦ s ○ s)
    _ = (𝓤 α).lift' fun s ↦ gen s ○ gen s := by
      rw [lift'_lift'_assoc]
      · exact monotone_gen
      · exact monotone_id.relComp monotone_id
    _ ≤ (𝓤 α).lift' fun s ↦ gen <| s ○ s := lift'_mono' fun _ _hs => subset_gen_relComp
    _ = ((𝓤 α).lift' fun s : SetRel α α => s ○ s).lift' gen := by
      rw [lift'_lift'_assoc]
      · exact monotone_id.relComp monotone_id
      · exact monotone_gen
    _ ≤ (𝓤 α).lift' gen := lift'_mono comp_le_uniformity le_rfl

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :

theorem mem_uniformity {s : Set (CauchyFilter α × CauchyFilter α)} :
    s ∈ 𝓤 (CauchyFilter α) ↔ ∃ t ∈ 𝓤 α, gen t ⊆ s :=
  mem_lift'_sets monotone_gen

theorem mem_uniformity' {s : Set (CauchyFilter α × CauchyFilter α)} :
    s ∈ 𝓤 (CauchyFilter α) ↔ ∃ t ∈ 𝓤 α, ∀ f g : CauchyFilter α, t ∈ f.1 ×ˢ g.1 → (f, g) ∈ s := by
  refine mem_uniformity.trans (exists_congr (fun t => and_congr_right_iff.mpr (fun _h => ?_)))
  exact ⟨fun h _f _g ht => h ht, fun h _p hp => h _ _ hp⟩

def pureCauchy (a : α) : CauchyFilter α :=
  ⟨pure a, cauchy_pure⟩

theorem isUniformInducing_pureCauchy : IsUniformInducing (pureCauchy : α → CauchyFilter α) :=
  ⟨have : (preimage fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ∘ gen = id :=
      funext fun s =>
        Set.ext fun ⟨a₁, a₂⟩ => by simp [preimage, gen, pureCauchy]
    calc
      comap (fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ((𝓤 α).lift' gen) =
          (𝓤 α).lift' ((preimage fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ∘ gen) :=
        comap_lift'_eq
      _ = 𝓤 α := by simp [this]
      ⟩

theorem isUniformEmbedding_pureCauchy : IsUniformEmbedding (pureCauchy : α → CauchyFilter α) where
  __ := isUniformInducing_pureCauchy
  injective _a₁ _a₂ h := pure_injective <| Subtype.ext_iff.1 h

theorem denseRange_pureCauchy : DenseRange (pureCauchy : α → CauchyFilter α) := fun f => by
  have h_ex : ∀ s ∈ 𝓤 (CauchyFilter α), ∃ y : α, (f, pureCauchy y) ∈ s := fun s hs =>
    let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs
    let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁
    have : t' ∈ f.val ×ˢ f.val := f.property.right ht'₁
    let ⟨t, ht, (h : t ×ˢ t ⊆ t')⟩ := mem_prod_same_iff.mp this
    let ⟨x, (hx : x ∈ t)⟩ := f.property.left.nonempty_of_mem ht
    have : t'' ∈ f.val ×ˢ pure x :=
      mem_prod_iff.mpr
        ⟨t, ht, { y : α | (x, y) ∈ t' }, h <| mk_mem_prod hx hx,
          fun ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩ =>
          ht'₂ <| SetRel.prodMk_mem_comp (@h (a, x) ⟨h₁, hx⟩) h₂⟩
    ⟨x, ht''₂ <| by dsimp [gen]; exact this⟩
  simp only [closure_eq_cluster_pts, ClusterPt, nhds_eq_uniformity, lift'_inf_principal_eq,
    Set.inter_comm _ (range pureCauchy), mem_setOf_eq]
  refine (lift'_neBot_iff ?_).mpr (fun s hs => ?_)
  · exact monotone_const.inter monotone_preimage
  · let ⟨y, hy⟩ := h_ex s hs
    have : pureCauchy y ∈ range pureCauchy ∩ { y : CauchyFilter α | (f, y) ∈ s } :=
      ⟨mem_range_self y, hy⟩
    exact ⟨_, this⟩

theorem isDenseInducing_pureCauchy : IsDenseInducing (pureCauchy : α → CauchyFilter α) :=
  isUniformInducing_pureCauchy.isDenseInducing denseRange_pureCauchy

theorem isDenseEmbedding_pureCauchy : IsDenseEmbedding (pureCauchy : α → CauchyFilter α) :=
  isUniformEmbedding_pureCauchy.isDenseEmbedding denseRange_pureCauchy

theorem nonempty_cauchyFilter_iff : Nonempty (CauchyFilter α) ↔ Nonempty α := by
  constructor <;> rintro ⟨c⟩
  · have := eq_univ_iff_forall.1 isDenseEmbedding_pureCauchy.isDenseInducing.closure_range c
    obtain ⟨_, ⟨_, a, _⟩⟩ := mem_closure_iff.1 this _ isOpen_univ trivial
    exact ⟨a⟩
  · exact ⟨pureCauchy c⟩

-- INSTANCE (free from Core): :

end

-- INSTANCE (free from Core): [Inhabited

-- INSTANCE (free from Core): [h

section Extend

open Classical in

def extend (f : α → β) : CauchyFilter α → β :=
  if UniformContinuous f then isDenseInducing_pureCauchy.extend f
  else fun x => f (nonempty_cauchyFilter_iff.1 ⟨x⟩).some

section T0Space

variable [T0Space β]

theorem extend_pureCauchy {f : α → β} (hf : UniformContinuous f) (a : α) :
    extend f (pureCauchy a) = f a := by
  rw [extend, if_pos hf]
  exact uniformly_extend_of_ind isUniformInducing_pureCauchy denseRange_pureCauchy hf _

end T0Space

variable [CompleteSpace β]

theorem uniformContinuous_extend {f : α → β} : UniformContinuous (extend f) := by
  by_cases hf : UniformContinuous f
  · rw [extend, if_pos hf]
    exact uniformContinuous_uniformly_extend isUniformInducing_pureCauchy denseRange_pureCauchy hf
  · rw [extend, if_neg hf]
    exact uniformContinuous_of_const fun a _b => by congr

end Extend

theorem inseparable_iff {f g : CauchyFilter α} : Inseparable f g ↔ f.1 ×ˢ g.1 ≤ 𝓤 α :=
  (basis_uniformity (basis_sets _)).inseparable_iff_uniformity

theorem inseparable_iff_of_le_nhds {f g : CauchyFilter α} {a b : α}
    (ha : f.1 ≤ 𝓝 a) (hb : g.1 ≤ 𝓝 b) : Inseparable a b ↔ Inseparable f g := by
  rw [← tendsto_id'] at ha hb
  rw [inseparable_iff, (ha.comp tendsto_fst).inseparable_iff_uniformity (hb.comp tendsto_snd)]
  simp only [Function.comp_apply, id_eq, Prod.mk.eta, ← Function.id_def, tendsto_id']

theorem inseparable_lim_iff [CompleteSpace α] {f g : CauchyFilter α} :
    haveI := f.2.1.nonempty; Inseparable (lim f.1) (lim g.1) ↔ Inseparable f g :=
  inseparable_iff_of_le_nhds f.2.le_nhds_lim g.2.le_nhds_lim

end

theorem cauchyFilter_eq {α : Type*} [UniformSpace α] [CompleteSpace α] [T0Space α]
    {f g : CauchyFilter α} :
    haveI := f.2.1.nonempty; lim f.1 = lim g.1 ↔ Inseparable f g := by
  rw [← inseparable_iff_eq, inseparable_lim_iff]

theorem separated_pureCauchy_injective {α : Type*} [UniformSpace α] [T0Space α] :
    Function.Injective fun a : α => SeparationQuotient.mk (pureCauchy a) := fun a b h ↦
  Inseparable.eq <| (inseparable_iff_of_le_nhds (pure_le_nhds a) (pure_le_nhds b)).2 <|
    SeparationQuotient.mk_eq_mk.1 h

end

end CauchyFilter

open CauchyFilter Set

namespace UniformSpace

variable (α : Type*) [UniformSpace α]

variable {β : Type*} [UniformSpace β]

variable {γ : Type*} [UniformSpace γ]

def Completion := SeparationQuotient (CauchyFilter α)

namespace Completion

-- INSTANCE (free from Core): inhabited

-- INSTANCE (free from Core): uniformSpace

-- INSTANCE (free from Core): completeSpace

-- INSTANCE (free from Core): t0Space

variable {α} in
