/-
Extracted from Topology/Separation/SeparatedNhds.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Separated neighbourhoods

This file defines the predicates `SeparatedNhds` and `HasSeparatingCover`, which are used in
formulating separation axioms for topological spaces.

## Main definitions

* `SeparatedNhds`: Two `Set`s are separated by neighbourhoods if they are contained in disjoint
  open sets.
* `HasSeparatingCover`: A set has a countable cover that can be used with
  `hasSeparatingCovers_iff_separatedNhds` to witness when two `Set`s have `SeparatedNhds`.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* [Willard's *General Topology*][zbMATH02107988]
-/

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

def SeparatedNhds : Set X → Set X → Prop := fun s t : Set X =>
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ s ⊆ U ∧ t ⊆ V ∧ Disjoint U V

theorem separatedNhds_iff_disjoint {s t : Set X} : SeparatedNhds s t ↔ Disjoint (𝓝ˢ s) (𝓝ˢ t) := by
  simp only [(hasBasis_nhdsSet s).disjoint_iff (hasBasis_nhdsSet t), SeparatedNhds, ←
    exists_and_left, and_assoc, and_comm, and_left_comm]

alias ⟨SeparatedNhds.disjoint_nhdsSet, _⟩ := separatedNhds_iff_disjoint

def HasSeparatingCover : Set X → Set X → Prop := fun s t ↦
  ∃ u : ℕ → Set X, s ⊆ ⋃ n, u n ∧ ∀ n, IsOpen (u n) ∧ Disjoint (closure (u n)) t

theorem hasSeparatingCovers_iff_separatedNhds {s t : Set X} :
    HasSeparatingCover s t ∧ HasSeparatingCover t s ↔ SeparatedNhds s t := by
  constructor
  · rintro ⟨⟨u, u_cov, u_props⟩, ⟨v, v_cov, v_props⟩⟩
    have open_lemma : ∀ (u₀ a : ℕ → Set X), (∀ n, IsOpen (u₀ n)) →
      IsOpen (⋃ n, u₀ n \ closure (a n)) := fun _ _ u₀i_open ↦
        isOpen_iUnion fun i ↦ (u₀i_open i).sdiff isClosed_closure
    have cover_lemma : ∀ (h₀ : Set X) (u₀ v₀ : ℕ → Set X),
        (h₀ ⊆ ⋃ n, u₀ n) → (∀ n, Disjoint (closure (v₀ n)) h₀) →
        (h₀ ⊆ ⋃ n, u₀ n \ closure (⋃ m ≤ n, v₀ m)) :=
        fun h₀ u₀ v₀ h₀_cov dis x xinh ↦ by
      rcases h₀_cov xinh with ⟨un, ⟨n, rfl⟩, xinun⟩
      simp only [mem_iUnion]
      refine ⟨n, xinun, ?_⟩
      simp_all only [closure_iUnion₂_le_nat, disjoint_right, mem_iUnion,
        exists_false, not_false_eq_true]
    refine
      ⟨⋃ n : ℕ, u n \ (closure (⋃ m ≤ n, v m)),
       ⋃ n : ℕ, v n \ (closure (⋃ m ≤ n, u m)),
       open_lemma u (fun n ↦ ⋃ m ≤ n, v m) (fun n ↦ (u_props n).1),
       open_lemma v (fun n ↦ ⋃ m ≤ n, u m) (fun n ↦ (v_props n).1),
       cover_lemma s u v u_cov (fun n ↦ (v_props n).2),
       cover_lemma t v u v_cov (fun n ↦ (u_props n).2),
       ?_⟩
    rw [Set.disjoint_left]
    rintro x ⟨un, ⟨n, rfl⟩, xinun⟩
    suffices ∀ (m : ℕ), x ∈ v m → x ∈ closure (⋃ m' ∈ {m' | m' ≤ m}, u m') by simpa
    intro m xinvm
    have n_le_m : n ≤ m := by
      by_contra m_gt_n
      exact xinun.2 (subset_closure (mem_biUnion (le_of_lt (not_le.mp m_gt_n)) xinvm))
    exact subset_closure (mem_biUnion n_le_m xinun.1)
  · rintro ⟨U, V, U_open, V_open, h_sub_U, k_sub_V, UV_dis⟩
    exact
      ⟨⟨fun _ ↦ U,
        h_sub_U.trans (iUnion_const U).symm.subset,
        fun _ ↦
          ⟨U_open, disjoint_of_subset (fun ⦃a⦄ a ↦ a) k_sub_V (UV_dis.closure_left V_open)⟩⟩,
       ⟨fun _ ↦ V,
        k_sub_V.trans (iUnion_const V).symm.subset,
        fun _ ↦
          ⟨V_open, disjoint_of_subset (fun ⦃a⦄ a ↦ a) h_sub_U (UV_dis.closure_right U_open).symm⟩⟩⟩

theorem Set.hasSeparatingCover_empty_left (s : Set X) : HasSeparatingCover ∅ s :=
  ⟨fun _ ↦ ∅, empty_subset (⋃ _, ∅),
   fun _ ↦ ⟨isOpen_empty, by simp only [closure_empty, empty_disjoint]⟩⟩

theorem Set.hasSeparatingCover_empty_right (s : Set X) : HasSeparatingCover s ∅ :=
  ⟨fun _ ↦ univ, (subset_univ s).trans univ.iUnion_const.symm.subset,
   fun _ ↦ ⟨isOpen_univ, by apply disjoint_empty⟩⟩

theorem HasSeparatingCover.mono {s₁ s₂ t₁ t₂ : Set X} (sc_st : HasSeparatingCover s₂ t₂)
    (s_sub : s₁ ⊆ s₂) (t_sub : t₁ ⊆ t₂) : HasSeparatingCover s₁ t₁ := by
  obtain ⟨u, u_cov, u_props⟩ := sc_st
  exact
    ⟨u,
     s_sub.trans u_cov,
     fun n ↦
       ⟨(u_props n).1,
        disjoint_of_subset (fun ⦃_⦄ a ↦ a) t_sub (u_props n).2⟩⟩

namespace SeparatedNhds

variable {s s₁ s₂ t t₁ t₂ u : Set X}
