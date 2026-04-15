/-
Extracted from Combinatorics/SimpleGraph/Extremal/Basic.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Extremal graph theory

This file introduces basic definitions for extremal graph theory, including extremal numbers.

## Main definitions

* `SimpleGraph.IsExtremal` is the predicate that `G` has the maximum number of edges of any simple
  graph, with fixed vertices, satisfying `p`.

* `SimpleGraph.extremalNumber` is the maximum number of edges in a `H`-free simple graph on `n`
  vertices.

  If `H` is contained in all simple graphs on `n` vertices, then this is `0`.
-/

assert_not_exists Field

open Finset Fintype

namespace SimpleGraph

section IsExtremal

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def IsExtremal (G : SimpleGraph V) [DecidableRel G.Adj] (p : SimpleGraph V → Prop) :=
  p G ∧ ∀ ⦃G' : SimpleGraph V⦄ [DecidableRel G'.Adj], p G' → #G'.edgeFinset ≤ #G.edgeFinset

open Classical in

theorem exists_isExtremal_iff_exists (p : SimpleGraph V → Prop) :
    (∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, G.IsExtremal p) ↔ ∃ G, p G := by
  refine ⟨fun ⟨_, _, h⟩ ↦ ⟨_, h.1⟩, fun ⟨G, hp⟩ ↦ ?_⟩
  obtain ⟨G', hp', h⟩ := by
    apply exists_max_image { G | p G } (#·.edgeFinset)
    use G, by simpa using hp
  use G', inferInstanceAs (DecidableRel G'.Adj)
  exact ⟨by simpa using hp', fun _ _ hp ↦ by convert h _ (by simpa using hp)⟩

theorem exists_isExtremal_free {W : Type*} {H : SimpleGraph W} (h : H ≠ ⊥) :
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, G.IsExtremal H.Free :=
  (exists_isExtremal_iff_exists H.Free).mpr ⟨⊥, free_bot h⟩

open Classical in

theorem IsExtremal.le_iff_eq
    {p : SimpleGraph V → Prop} (hG : G.IsExtremal p) {H : SimpleGraph V} (hH : p H) :
    G ≤ H ↔ G = H :=
  ⟨fun hGH ↦ edgeFinset_inj.1 <|
    eq_of_subset_of_card_le (edgeFinset_subset_edgeFinset.2 hGH) (hG.2 hH), le_of_eq⟩

end IsExtremal

section ExtremalNumber

open Classical in

noncomputable def extremalNumber (n : ℕ) {W : Type*} (H : SimpleGraph W) : ℕ :=
  sup { G : SimpleGraph (Fin n) | H.Free G } (#·.edgeFinset)

variable {n : ℕ} {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

open Classical in

theorem extremalNumber_of_fintypeCard_eq [Fintype V] (hc : card V = n) :
    extremalNumber n H = sup { G : SimpleGraph V | H.Free G } (#·.edgeFinset) := by
  let e := Fintype.equivFinOfCardEq hc
  rw [extremalNumber, le_antisymm_iff]
  and_intros
  on_goal 1 =>
    replace e := e.symm
  all_goals
  rw [Finset.sup_le_iff]
  intro G h
  let G' := G.map e.toEmbedding
  replace h' : G' ∈ univ.filter (H.Free ·) := by
    rw [mem_filter, ← free_congr .refl (.map e G)]
    simpa using h
  rw [Iso.card_edgeFinset_eq (.map e G)]
  convert @le_sup _ _ _ _ { G | H.Free G } (#·.edgeFinset) G' h'

variable [Fintype V] [DecidableRel G.Adj]

theorem card_edgeFinset_le_extremalNumber (h : H.Free G) :
    #G.edgeFinset ≤ extremalNumber (card V) H := by
  rw [extremalNumber_of_fintypeCard_eq rfl]
  convert @le_sup _ _ _ _ { G | H.Free G } (#·.edgeFinset) G (by simpa using h)

theorem IsContained.of_extremalNumber_lt_card_edgeFinset
    (h : extremalNumber (card V) H < #G.edgeFinset) : H ⊑ G := by
  contrapose h; push Not
  exact card_edgeFinset_le_extremalNumber h

theorem extremalNumber_le_iff (H : SimpleGraph W) (m : ℕ) :
    extremalNumber (card V) H ≤ m ↔
      ∀ ⦃G : SimpleGraph V⦄ [DecidableRel G.Adj], H.Free G → #G.edgeFinset ≤ m := by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.sup_le_iff, mem_filter_univ]
  exact ⟨fun h _ _ h' ↦ by convert h _ h', fun h _ h' ↦ by convert h h'⟩

theorem lt_extremalNumber_iff (H : SimpleGraph W) (m : ℕ) :
    m < extremalNumber (card V) H ↔
      ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, H.Free G ∧ m < #G.edgeFinset := by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.lt_sup_iff, mem_filter_univ]
  exact ⟨fun ⟨_, h, h'⟩ ↦ ⟨_, _, h, h'⟩, fun ⟨_, _, h, h'⟩ ↦ ⟨_, h, by convert h'⟩⟩

variable {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]
