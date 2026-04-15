/-
Extracted from Analysis/Convex/Caratheodory.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Carathéodory's convexity theorem

Convex hull can be regarded as a refinement of affine span. Both are closure operators but whereas
convex hull takes values in the lattice of convex subsets, affine span takes values in the much
coarser sublattice of affine subspaces.

The cost of this refinement is that one no longer has bases. However Carathéodory's convexity
theorem offers some compensation. Given a set `s` together with a point `x` in its convex hull,
Carathéodory says that one may find an affine-independent family of elements `s` whose convex hull
contains `x`. Thus the difference from the case of affine span is that the affine-independent family
depends on `x`.

In particular, in finite dimensions Carathéodory's theorem implies that the convex hull of a set `s`
in `𝕜ᵈ` is the union of the convex hulls of the `(d + 1)`-tuples in `s`.

## Main results

* `convexHull_eq_union`: Carathéodory's convexity theorem

## Implementation details

This theorem was formalized as part of the Sphere Eversion project.

## Tags
convex hull, caratheodory

-/

open Set Finset

universe u

variable {𝕜 : Type*} {E : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

namespace Caratheodory

variable {s : Set E} {x : E}

noncomputable def minCardFinsetOfMemConvexHull (hx : x ∈ convexHull 𝕜 s) : Finset E :=
  Function.argminOn Finset.card { t | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } <| by
    simpa only [convexHull_eq_union_convexHull_finite_subsets s, exists_prop, mem_iUnion] using hx

variable (hx : x ∈ convexHull 𝕜 s)

theorem minCardFinsetOfMemConvexHull_subseteq : ↑(minCardFinsetOfMemConvexHull hx) ⊆ s :=
  (Function.argminOn_mem _ { t : Finset E | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).1

theorem mem_minCardFinsetOfMemConvexHull :
    x ∈ convexHull 𝕜 (minCardFinsetOfMemConvexHull hx : Set E) :=
  (Function.argminOn_mem _ { t : Finset E | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).2

theorem minCardFinsetOfMemConvexHull_nonempty : (minCardFinsetOfMemConvexHull hx).Nonempty := by
  rw [← Finset.coe_nonempty, ← @convexHull_nonempty_iff 𝕜]
  exact ⟨x, mem_minCardFinsetOfMemConvexHull hx⟩

theorem minCardFinsetOfMemConvexHull_card_le_card {t : Finset E} (ht₁ : ↑t ⊆ s)
    (ht₂ : x ∈ convexHull 𝕜 (t : Set E)) : #(minCardFinsetOfMemConvexHull hx) ≤ #t :=
  Function.argminOn_le _ _ (by exact ⟨ht₁, ht₂⟩)

theorem affineIndependent_minCardFinsetOfMemConvexHull :
    AffineIndependent 𝕜 ((↑) : minCardFinsetOfMemConvexHull hx → E) := by
  let k := #(minCardFinsetOfMemConvexHull hx) - 1
  have hk : #(minCardFinsetOfMemConvexHull hx) = k + 1 :=
    (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (minCardFinsetOfMemConvexHull_nonempty hx))).symm
  classical
  by_contra h
  obtain ⟨p, hp⟩ := mem_convexHull_erase h (mem_minCardFinsetOfMemConvexHull hx)
  have contra := minCardFinsetOfMemConvexHull_card_le_card hx (Set.Subset.trans
    (Finset.erase_subset (p : E) (minCardFinsetOfMemConvexHull hx))
    (minCardFinsetOfMemConvexHull_subseteq hx)) hp
  rw [← not_lt] at contra
  apply contra
  rw [card_erase_of_mem p.2, hk]
  exact lt_add_one _

end Caratheodory

variable {s : Set E}

theorem convexHull_eq_union : convexHull 𝕜 s =
    ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : AffineIndependent 𝕜 ((↑) : t → E)), convexHull 𝕜 ↑t := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [exists_prop, Set.mem_iUnion]
    exact ⟨Caratheodory.minCardFinsetOfMemConvexHull hx,
      Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx,
      Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  · iterate 3 convert Set.iUnion_subset _; intro
    exact convexHull_mono ‹_›

theorem eq_pos_convex_span_of_mem_convexHull {x : E} (hx : x ∈ convexHull 𝕜 s) :
    ∃ (ι : Sort (u + 1)) (_ : Fintype ι),
      ∃ (z : ι → E) (w : ι → 𝕜), Set.range z ⊆ s ∧ AffineIndependent 𝕜 z ∧ (∀ i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  rw [convexHull_eq_union] at hx
  simp only [exists_prop, Set.mem_iUnion] at hx
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx
  simp only [t.convexHull_eq, Set.mem_setOf_eq] at ht₃
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := ht₃
  let t' := {i ∈ t | w i ≠ 0}
  refine ⟨t', t'.fintypeCoeSort, ((↑) : t' → E), w ∘ ((↑) : t' → E), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subtype.range_coe_subtype]
    exact Subset.trans (Finset.filter_subset _ t) ht₁
  · exact ht₂.comp_embedding ⟨_, inclusion_injective (Finset.filter_subset (fun i => w i ≠ 0) t)⟩
  · exact fun i =>
      (hw₁ _ (Finset.mem_filter.mp i.2).1).lt_of_ne (Finset.mem_filter.mp i.property).2.symm
  · simp only [univ_eq_attach, Function.comp_apply]
    rw [Finset.sum_attach, Finset.sum_filter_ne_zero, hw₂]
  · change (∑ i ∈ t'.attach, (fun e => w e • e) ↑i) = x
    rw [Finset.sum_attach (f := fun e => w e • e), Finset.sum_filter_of_ne]
    · rw [t.centerMass_eq_of_sum_1 id hw₂] at hw₃
      exact hw₃
    · intro e _ hwe contra
      apply hwe
      rw [contra, zero_smul]
