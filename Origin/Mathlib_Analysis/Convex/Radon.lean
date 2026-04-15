/-
Extracted from Analysis/Convex/Radon.lean
Genuine: 9 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Separation.Basic

/-!
# Radon's theorem on convex sets

Radon's theorem states that any affine dependent set can be partitioned into two sets whose convex
hulls intersect nontrivially.

As a corollary, we prove Helly's theorem, which is a basic result in discrete geometry on the
intersection of convex sets. Let `X₁, ⋯, Xₙ` be a finite family of convex sets in `ℝᵈ` with
`n ≥ d + 1`. The theorem states that if any `d + 1` sets from this family intersect nontrivially,
then the whole family intersect nontrivially. For the infinite family of sets it is not true, as
example of `Set.Ioo 0 (1 / n)` for `n : ℕ` shows. But the statement is true, if we assume
compactness of sets (see `helly_theorem_compact`)

## Tags

convex hull, affine independence, Radon, Helly
-/

open Fintype Finset Set

namespace Convex

variable {ι 𝕜 E : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem radon_partition {f : ι → E} (h : ¬ AffineIndependent 𝕜 f) :
    ∃ I, (convexHull 𝕜 (f '' I) ∩ convexHull 𝕜 (f '' Iᶜ)).Nonempty := by
  rw [affineIndependent_iff] at h
  push_neg at h
  obtain ⟨s, w, h_wsum, h_vsum, nonzero_w_index, h1, h2⟩ := h
  let I : Finset ι := {i ∈ s | 0 ≤ w i}
  let J : Finset ι := {i ∈ s | w i < 0}
  let p : E := centerMass I w f -- point of intersection
  have hJI : ∑ j ∈ J, w j + ∑ i ∈ I, w i = 0 := by
    simpa only [h_wsum, not_lt] using sum_filter_add_sum_filter_not s (fun i ↦ w i < 0) w
  have hI : 0 < ∑ i ∈ I, w i := by
    rcases exists_pos_of_sum_zero_of_exists_nonzero _ h_wsum ⟨nonzero_w_index, h1, h2⟩
      with ⟨pos_w_index, h1', h2'⟩
    exact sum_pos' (fun _i hi ↦ (mem_filter.1 hi).2)
      ⟨pos_w_index, by simp only [I, mem_filter, h1', h2'.le, and_self, h2']⟩
  have hp : centerMass J w f = p := centerMass_of_sum_add_sum_eq_zero hJI <| by
    simpa only [← h_vsum, not_lt] using sum_filter_add_sum_filter_not s (fun i ↦ w i < 0) _
  refine ⟨I, p, ?_, ?_⟩
  · exact centerMass_mem_convexHull _ (fun _i hi ↦ (mem_filter.mp hi).2) hI
      (fun _i hi ↦ mem_image_of_mem _ hi)
  rw [← hp]
  refine centerMass_mem_convexHull_of_nonpos _ (fun _ hi ↦ (mem_filter.mp hi).2.le) ?_
    (fun _i hi ↦ mem_image_of_mem _ fun hi' ↦ ?_)
  · linarith only [hI, hJI]
  · exact (mem_filter.mp hi').2.not_lt (mem_filter.mp hi).2

open Module

private lemma helly_theorem_corner {F : ι → Set E} {s : Finset ι}
    (h_card_small : #s ≤ finrank 𝕜 E + 1)
    (h_inter : ∀ I ⊆ s, #I ≤ finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ s, F i).Nonempty := h_inter s (by simp) h_card_small

variable [FiniteDimensional 𝕜 E]

theorem helly_theorem' {F : ι → Set E} {s : Finset ι}
    (h_convex : ∀ i ∈ s, Convex 𝕜 (F i))
    (h_inter : ∀ I ⊆ s, #I ≤ finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ s, F i).Nonempty := by
  classical
  obtain h_card | h_card := lt_or_le #s (finrank 𝕜 E + 1)
  · exact helly_theorem_corner (le_of_lt h_card) h_inter
  generalize hn : #s = n
  rw [hn] at h_card
  induction' n, h_card using Nat.le_induction with k h_card hk generalizing ι
  · exact helly_theorem_corner (le_of_eq hn) h_inter
  /- Construct a family of vectors indexed by `ι` such that the vector corresponding to `i : ι`
  is an arbitrary element of the intersection of all `F j` except `F i`. -/
  let a (i : s) : E := Set.Nonempty.some (s := ⋂ j ∈ s.erase i, F j) <| by
    apply hk (s := s.erase i)
    · exact fun i hi ↦ h_convex i (mem_of_mem_erase hi)
    · intro J hJ_ss hJ_card
      exact h_inter J (subset_trans hJ_ss (erase_subset i.val s)) hJ_card
    · simp only [coe_mem, card_erase_of_mem]; omega
  /- This family of vectors is not affine independent because the number of them exceeds the
  dimension of the space. -/
  have h_ind : ¬AffineIndependent 𝕜 a := by
    rw [← finrank_vectorSpan_le_iff_not_affineIndependent 𝕜 a (n := (k - 1))]
    · exact (Submodule.finrank_le (vectorSpan 𝕜 (range a))).trans (Nat.le_pred_of_lt h_card)
    · simp only [card_coe]; omega
  /- Use `radon_partition` to conclude there is a subset `I` of `s` and a point `p : E` which
  lies in the convex hull of either `a '' I` or `a '' Iᶜ`. We claim that `p ∈ ⋂ i ∈ s, F i`. -/
  obtain ⟨I, p, hp_I, hp_Ic⟩ := radon_partition h_ind
  use p
  apply mem_biInter
  intro i hi
  let i : s := ⟨i, hi⟩
  /- It suffices to show that for any subcollection `J` of `s` containing `i`, the convex
  hull of `a '' (s \ J)` is contained in `F i`. -/
  suffices ∀ J : Set s, (i ∈ J) → (convexHull 𝕜) (a '' Jᶜ) ⊆ F i by
    by_cases h : i ∈ I
    · exact this I h hp_Ic
    · apply this Iᶜ h; rwa [compl_compl]
  /- Given any subcollection `J` of `ι` containing `i`, because `F i` is convex, we need only
  show that `a j ∈ F i` for each `j ∈ s \ J`. -/
  intro J hi
  rw [convexHull_subset_iff (h_convex i.1 i.2)]
  rintro v ⟨j, hj, hj_v⟩
  rw [← hj_v]
  /- Since `j ∈ Jᶜ` and `i ∈ J`, we conclude that `i ≠ j`, and hence by the definition of `a`:
  `a j ∈ ⋂ F '' (Set.univ \ {j}) ⊆ F i`. -/
  apply mem_of_subset_of_mem (s₁ := ⋂ k ∈ (s.erase j), F k)
  · apply biInter_subset_of_mem
    simp only [erase_val]
    suffices h : i.val ∈ s.erase j by assumption
    simp only [mem_erase]
    constructor
    · exact fun h' ↦ hj ((show i = j from SetCoe.ext h') ▸ hi)
    · assumption
  · apply Nonempty.some_mem

theorem helly_theorem {F : ι → Set E} {s : Finset ι}
    (h_card : finrank 𝕜 E + 1 ≤ #s)
    (h_convex : ∀ i ∈ s, Convex 𝕜 (F i))
    (h_inter : ∀ I ⊆ s, #I = finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ s, F i).Nonempty := by
  apply helly_theorem' h_convex
  intro I hI_ss hI_card
  obtain ⟨J, hI_ss_J, hJ_ss, hJ_card⟩ := exists_subsuperset_card_eq hI_ss hI_card h_card
  apply Set.Nonempty.mono <| biInter_mono hI_ss_J (fun _ _ ↦ Set.Subset.rfl)
  exact h_inter J hJ_ss hJ_card

theorem helly_theorem_set' {F : Finset (Set E)}
    (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_inter : ∀ G : Finset (Set E), G ⊆ F → #G ≤ finrank 𝕜 E + 1 → (⋂₀ G : Set E).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty := by
  classical -- for DecidableEq, required for the family version
  rw [show ⋂₀ F = ⋂ X ∈ F, (X : Set E) by ext; simp]
  apply helly_theorem' h_convex
  intro G hG_ss hG_card
  rw [show ⋂ X ∈ G, X = ⋂₀ G by ext; simp]
  exact h_inter G hG_ss hG_card

theorem helly_theorem_set {F : Finset (Set E)}
    (h_card : finrank 𝕜 E + 1 ≤ #F)
    (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_inter : ∀ G : Finset (Set E), G ⊆ F → #G = finrank 𝕜 E + 1 → (⋂₀ G : Set E).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty := by
  apply helly_theorem_set' h_convex
  intro I hI_ss hI_card
  obtain ⟨J, _, hJ_ss, hJ_card⟩ := exists_subsuperset_card_eq hI_ss hI_card h_card
  have : ⋂₀ (J : Set (Set E)) ⊆ ⋂₀ I := sInter_mono (by simpa [hI_ss])
  apply Set.Nonempty.mono this
  exact h_inter J hJ_ss (by omega)

theorem helly_theorem_compact' [TopologicalSpace E] [T2Space E] {F : ι → Set E}
    (h_convex : ∀ i, Convex 𝕜 (F i)) (h_compact : ∀ i, IsCompact (F i))
    (h_inter : ∀ I : Finset ι, #I ≤ finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i, F i).Nonempty := by
  classical
  /- If `ι` is empty the statement is trivial. -/
  cases' isEmpty_or_nonempty ι with _ h_nonempty
  · simp only [iInter_of_empty, Set.univ_nonempty]
  /- By the finite version of theorem, every finite subfamily has an intersection. -/
  have h_fin (I : Finset ι) : (⋂ i ∈ I, F i).Nonempty := by
    apply helly_theorem' (s := I) (𝕜 := 𝕜) (by simp [h_convex])
    exact fun J _ hJ_card ↦ h_inter J hJ_card
  /- The following is a clumsy proof that family of compact sets with the finite intersection
  property has a nonempty intersection. -/
  have i0 : ι := Nonempty.some h_nonempty
  rw [show ⋂ i, F i = (F i0) ∩ ⋂ i, F i by simp [iInter_subset]]
  apply IsCompact.inter_iInter_nonempty
  · exact h_compact i0
  · intro i
    exact (h_compact i).isClosed
  · intro I
    simpa using h_fin ({i0} ∪ I)

theorem helly_theorem_compact [TopologicalSpace E] [T2Space E] {F : ι → Set E}
    (h_card : finrank 𝕜 E + 1 ≤ ENat.card ι)
    (h_convex : ∀ i, Convex 𝕜 (F i)) (h_compact : ∀ i, IsCompact (F i))
    (h_inter : ∀ I : Finset ι, #I = finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i, F i).Nonempty := by
  apply helly_theorem_compact' h_convex h_compact
  intro I hI_card
  have hJ : ∃ J : Finset ι, I ⊆ J ∧ #J = finrank 𝕜 E + 1 := by
    by_cases h : Infinite ι
    · exact Infinite.exists_superset_card_eq _ _ hI_card
    · have : Finite ι := Finite.of_not_infinite h
      have : Fintype ι := Fintype.ofFinite ι
      apply exists_superset_card_eq hI_card
      simp only [ENat.card_eq_coe_fintype_card] at h_card
      rwa [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le] at h_card
  obtain ⟨J, hJ_ss, hJ_card⟩ := hJ
  apply Set.Nonempty.mono <| biInter_mono hJ_ss (by intro _ _; rfl)
  exact h_inter J hJ_card

theorem helly_theorem_set_compact' [TopologicalSpace E] [T2Space E] {F : Set (Set E)}
    (h_convex : ∀ X ∈ F, Convex 𝕜 X) (h_compact : ∀ X ∈ F, IsCompact X)
    (h_inter : ∀ G : Finset (Set E), (G : Set (Set E)) ⊆ F → #G ≤ finrank 𝕜 E + 1 →
    (⋂₀ G : Set E).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty := by
  classical -- for DecidableEq, required for the family version
  rw [show ⋂₀ F = ⋂ X : F, (X : Set E) by ext; simp]
  refine helly_theorem_compact' (F := fun x : F ↦ x.val)
    (fun X ↦ h_convex X (by simp)) (fun X ↦ h_compact X (by simp)) ?_
  intro G _
  let G' : Finset (Set E) := image Subtype.val G
  rw [show ⋂ i ∈ G, ↑i = ⋂₀ (G' : Set (Set E)) by simp [G']]
  apply h_inter G'
  · simp [G']
  · apply le_trans card_image_le
    assumption

theorem helly_theorem_set_compact [TopologicalSpace E] [T2Space E] {F : Set (Set E)}
    (h_card : finrank 𝕜 E + 1 ≤ F.encard)
    (h_convex : ∀ X ∈ F, Convex 𝕜 X) (h_compact : ∀ X ∈ F, IsCompact X)
    (h_inter : ∀ G : Finset (Set E), (G : Set (Set E)) ⊆ F → #G = finrank 𝕜 E + 1 →
    (⋂₀ G : Set E).Nonempty) :
    (⋂₀ (F : Set (Set E))).Nonempty := by
  apply helly_theorem_set_compact' h_convex h_compact
  intro I hI_ss hI_card
  obtain ⟨J, _, hJ_ss, hJ_card⟩ := exists_superset_subset_encard_eq hI_ss (hkt := h_card)
    (by simpa only [encard_coe_eq_coe_finsetCard, ← ENat.coe_one, ← ENat.coe_add, Nat.cast_le])
  apply Set.Nonempty.mono <| sInter_mono (by simpa [hI_ss])
  have hJ_fin : Fintype J := Finite.fintype <| finite_of_encard_eq_coe hJ_card
  let J' := J.toFinset
  rw [← coe_toFinset J]
  apply h_inter J'
  · simpa [J']
  · rwa [encard_eq_coe_toFinset_card J, ← ENat.coe_one, ← ENat.coe_add, Nat.cast_inj] at hJ_card

end Convex
