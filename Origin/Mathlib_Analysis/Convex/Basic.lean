/-
Extracted from Analysis/Convex/Basic.lean
Genuine: 23 of 23 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Convex sets

In a 𝕜-vector space, we define the following property:
* `Convex 𝕜 s`: A set `s` is convex if for any two points `x y ∈ s` it includes `segment 𝕜 x y`.

We provide various equivalent versions, and prove that some specific sets are convex.

## TODO

Generalize all this file to affine spaces.
-/

variable {𝕜 E F β : Type*}

open LinearMap Set

open scoped Convex Pointwise

/-! ### Convexity of sets -/

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (s : Set E) {x : E}

def Convex : Prop :=
  ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s

variable {𝕜 s}

theorem Convex.starConvex (hs : Convex 𝕜 s) (hx : x ∈ s) : StarConvex 𝕜 x s :=
  hs hx

theorem convex_iff_segment_subset : Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → [x -[𝕜] y] ⊆ s :=
  forall₂_congr fun _ _ => starConvex_iff_segment_subset

theorem Convex.segment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    [x -[𝕜] y] ⊆ s :=
  convex_iff_segment_subset.1 h hx hy

theorem Convex.openSegment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    openSegment 𝕜 x y ⊆ s :=
  (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)

theorem convex_iff_add_mem : Convex 𝕜 s ↔
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s := by
  simp_rw [convex_iff_segment_subset, segment_subset_iff]

theorem convex_iff_pointwise_add_subset :
    Convex 𝕜 s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
  Iff.intro
    (by
      rintro hA a b ha hb hab w ⟨au, ⟨u, hu, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
      exact hA hu hv ha hb hab)
    fun h _ hx _ hy _ _ ha hb hab => (h ha hb hab) (Set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩)

alias ⟨Convex.set_combo_subset, _⟩ := convex_iff_pointwise_add_subset

theorem convex_empty : Convex 𝕜 (∅ : Set E) := fun _ => False.elim

theorem convex_univ : Convex 𝕜 (Set.univ : Set E) := fun _ _ => starConvex_univ _

theorem Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s ∩ t) :=
  fun _ hx => (hs hx.1).inter (ht hx.2)

theorem convex_sInter {S : Set (Set E)} (h : ∀ s ∈ S, Convex 𝕜 s) : Convex 𝕜 (⋂₀ S) := fun _ hx =>
  starConvex_sInter fun _ hs => h _ hs <| hx _ hs

theorem convex_iInter {ι : Sort*} {s : ι → Set E} (h : ∀ i, Convex 𝕜 (s i)) :
    Convex 𝕜 (⋂ i, s i) :=
  sInter_range s ▸ convex_sInter <| forall_mem_range.2 h

theorem convex_iInter₂ {ι : Sort*} {κ : ι → Sort*} {s : (i : ι) → κ i → Set E}
    (h : ∀ i j, Convex 𝕜 (s i j)) : Convex 𝕜 (⋂ (i) (j), s i j) :=
  convex_iInter fun i => convex_iInter <| h i

theorem Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
    Convex 𝕜 (s ×ˢ t) := fun _ hx => (hs hx.1).prod (ht hx.2)

theorem convex_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommMonoid (E i)] [∀ i, SMul 𝕜 (E i)]
    {s : Set ι} {t : ∀ i, Set (E i)} (ht : ∀ ⦃i⦄, i ∈ s → Convex 𝕜 (t i)) : Convex 𝕜 (s.pi t) :=
  fun _ hx => starConvex_pi fun _ hi => ht hi <| hx _ hi

theorem Directed.convex_iUnion {ι : Sort*} {s : ι → Set E} (hdir : Directed (· ⊆ ·) s)
    (hc : ∀ ⦃i : ι⦄, Convex 𝕜 (s i)) : Convex 𝕜 (⋃ i, s i) := by
  rintro x hx y hy a b ha hb hab
  rw [mem_iUnion] at hx hy ⊢
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩

theorem DirectedOn.convex_sUnion {c : Set (Set E)} (hdir : DirectedOn (· ⊆ ·) c)
    (hc : ∀ ⦃A : Set E⦄, A ∈ c → Convex 𝕜 A) : Convex 𝕜 (⋃₀ c) := by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).convex_iUnion fun A => hc A.2

theorem Convex.setOf_const_imp {P : Prop} (hs : Convex 𝕜 s) : Convex 𝕜 {x | P → x ∈ s} := by
  by_cases hP : P <;> simp [hP, hs, convex_univ]

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

theorem convex_iff_openSegment_subset [ZeroLEOneClass 𝕜] :
    Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → openSegment 𝕜 x y ⊆ s :=
  forall₂_congr fun _ => starConvex_iff_openSegment_subset

theorem convex_iff_forall_pos :
    Convex 𝕜 s ↔
      ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
  forall₂_congr fun _ => starConvex_iff_forall_pos

theorem convex_iff_pairwise_pos : Convex 𝕜 s ↔
    s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine convex_iff_forall_pos.trans ⟨fun h x hx y hy _ => h hx hy, ?_⟩
  intro h x hx y hy a b ha hb hab
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
  · exact h hx hy hxy ha hb hab

theorem Convex.starConvex_iff [ZeroLEOneClass 𝕜] (hs : Convex 𝕜 s) (h : s.Nonempty) :
    StarConvex 𝕜 x s ↔ x ∈ s :=
  ⟨fun hxs => hxs.mem h, hs.starConvex⟩

protected theorem Set.Subsingleton.convex {s : Set E} (h : s.Subsingleton) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.mpr (h.pairwise _)
