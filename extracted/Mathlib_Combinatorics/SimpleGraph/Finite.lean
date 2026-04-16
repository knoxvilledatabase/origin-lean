/-
Extracted from Combinatorics/SimpleGraph/Finite.lean
Genuine: 56 | Conflates: 0 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Sym.Card

noncomputable section

/-!
# Definitions for finite and locally finite graphs

This file defines finite versions of `edgeSet`, `neighborSet` and `incidenceSet` and proves some
of their basic properties. It also defines the notion of a locally finite graph, which is one
whose vertices have finite degree.

The design for finiteness is that each definition takes the smallest finiteness assumption
necessary. For example, `SimpleGraph.neighborFinset v` only requires that `v` have
finitely many neighbors.

## Main definitions

* `SimpleGraph.edgeFinset` is the `Finset` of edges in a graph, if `edgeSet` is finite
* `SimpleGraph.neighborFinset` is the `Finset` of vertices adjacent to a given vertex,
   if `neighborSet` is finite
* `SimpleGraph.incidenceFinset` is the `Finset` of edges containing a given vertex,
   if `incidenceSet` is finite

## Naming conventions

If the vertex type of a graph is finite, we refer to its cardinality as `CardVerts`
or `card_verts`.

## Implementation notes

* A locally finite graph is one with instances `Π v, Fintype (G.neighborSet v)`.
* Given instances `DecidableRel G.Adj` and `Fintype V`, then the graph
  is locally finite, too.
-/

open Finset Function

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) {e : Sym2 V}

section EdgeFinset

variable {G₁ G₂ : SimpleGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

abbrev edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet

@[norm_cast]
theorem coe_edgeFinset : (G.edgeFinset : Set (Sym2 V)) = G.edgeSet :=
  Set.coe_toFinset _

variable {G}

theorem mem_edgeFinset : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet :=
  Set.mem_toFinset

theorem not_isDiag_of_mem_edgeFinset : e ∈ G.edgeFinset → ¬e.IsDiag :=
  not_isDiag_of_mem_edgeSet _ ∘ mem_edgeFinset.1

theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp

theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂ := by simp

theorem edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by simp

@[gcongr] alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset

alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset

attribute [mono] edgeFinset_mono edgeFinset_strict_mono

@[simp]
theorem edgeFinset_bot : (⊥ : SimpleGraph V).edgeFinset = ∅ := by simp [edgeFinset]

@[simp]
theorem edgeFinset_sup [Fintype (edgeSet (G₁ ⊔ G₂))] [DecidableEq V] :
    (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset ∪ G₂.edgeFinset := by simp [edgeFinset]

@[simp]
theorem edgeFinset_inf [DecidableEq V] : (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset ∩ G₂.edgeFinset := by
  simp [edgeFinset]

@[simp]
theorem edgeFinset_sdiff [DecidableEq V] :
    (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ G₂.edgeFinset := by simp [edgeFinset]

lemma disjoint_edgeFinset : Disjoint G₁.edgeFinset G₂.edgeFinset ↔ Disjoint G₁ G₂ := by
  simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

lemma edgeFinset_eq_empty : G.edgeFinset = ∅ ↔ G = ⊥ := by
  rw [← edgeFinset_bot, edgeFinset_inj]

lemma edgeFinset_nonempty : G.edgeFinset.Nonempty ↔ G ≠ ⊥ := by
  rw [Finset.nonempty_iff_ne_empty, edgeFinset_eq_empty.ne]

theorem edgeFinset_card : #G.edgeFinset = Fintype.card G.edgeSet :=
  Set.toFinset_card _

@[simp]
theorem edgeSet_univ_card : #(univ : Finset G.edgeSet) = #G.edgeFinset :=
  Fintype.card_of_subtype G.edgeFinset fun _ => mem_edgeFinset

variable [Fintype V]

@[simp]
theorem edgeFinset_top [DecidableEq V] :
    (⊤ : SimpleGraph V).edgeFinset = ({e | ¬e.IsDiag} : Finset _) := by simp [← coe_inj]

theorem card_edgeFinset_top_eq_card_choose_two [DecidableEq V] :
    #(⊤ : SimpleGraph V).edgeFinset = (Fintype.card V).choose 2 := by
  simp_rw [Set.toFinset_card, edgeSet_top, Set.coe_setOf, ← Sym2.card_subtype_not_diag]

theorem card_edgeFinset_le_card_choose_two : #G.edgeFinset ≤ (Fintype.card V).choose 2 := by
  classical
  rw [← card_edgeFinset_top_eq_card_choose_two]
  exact card_le_card (edgeFinset_mono le_top)

end EdgeFinset

theorem edgeFinset_deleteEdges [DecidableEq V] [Fintype G.edgeSet] (s : Finset (Sym2 V))
    [Fintype (G.deleteEdges s).edgeSet] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset \ s := by
  ext e
  simp [edgeSet_deleteEdges]

section DeleteFar

variable {𝕜 : Type*} [OrderedRing 𝕜]
  [Fintype G.edgeSet] {p : SimpleGraph V → Prop} {r r₁ r₂ : 𝕜}

def DeleteFar (p : SimpleGraph V → Prop) (r : 𝕜) : Prop :=
  ∀ ⦃s⦄, s ⊆ G.edgeFinset → p (G.deleteEdges s) → r ≤ #s

variable {G}

theorem deleteFar_iff [Fintype (Sym2 V)] :
    G.DeleteFar p r ↔ ∀ ⦃H : SimpleGraph _⦄ [DecidableRel H.Adj],
      H ≤ G → p H → r ≤ #G.edgeFinset - #H.edgeFinset := by
  classical
  refine ⟨fun h H _ hHG hH ↦ ?_, fun h s hs hG ↦ ?_⟩
  · have := h (sdiff_subset (t := H.edgeFinset))
    simp only [deleteEdges_sdiff_eq_of_le hHG, edgeFinset_mono hHG, card_sdiff,
      card_le_card, coe_sdiff, coe_edgeFinset, Nat.cast_sub] at this
    exact this hH
  · classical
    simpa [card_sdiff hs, edgeFinset_deleteEdges, -Set.toFinset_card, Nat.cast_sub,
      card_le_card hs] using h (G.deleteEdges_le s) hG

alias ⟨DeleteFar.le_card_sub_card, _⟩ := deleteFar_iff

theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ ≤ r₂) : G.DeleteFar p r₁ := fun _ hs hG =>
  hr.trans <| h hs hG

end DeleteFar

section FiniteAt

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`Fintype (G.neighborSet v)`.

We define `G.neighborFinset v` to be the `Finset` version of `G.neighborSet v`.
Use `neighborFinset_eq_filter` to rewrite this definition as a `Finset.filter` expression.
-/

variable (v) [Fintype (G.neighborSet v)]

def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset

@[simp]
theorem mem_neighborFinset (w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_toFinset

theorem not_mem_neighborFinset_self : v ∉ G.neighborFinset v := by simp

theorem neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v} :=
  Finset.disjoint_singleton_right.mpr <| not_mem_neighborFinset_self _ _

theorem singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v) :=
  Finset.disjoint_singleton_left.mpr <| not_mem_neighborFinset_self _ _

def degree : ℕ := #(G.neighborFinset v)

@[simp]
theorem card_neighborFinset_eq_degree : #(G.neighborFinset v) = G.degree v := rfl

@[simp]
theorem card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v :=
  (Set.toFinset_card _).symm

theorem degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.Adj v w := by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighborFinset]

theorem degree_compl [Fintype (Gᶜ.neighborSet v)] [Fintype V] :
    Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  classical
    rw [← card_neighborSet_union_compl_neighborSet G v, Set.toFinset_union]
    simp [card_union_of_disjoint (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v))]

instance incidenceSetFintype [DecidableEq V] : Fintype (G.incidenceSet v) :=
  Fintype.ofEquiv (G.neighborSet v) (G.incidenceSetEquivNeighborSet v).symm

def incidenceFinset [DecidableEq V] : Finset (Sym2 V) :=
  (G.incidenceSet v).toFinset

@[simp]
theorem card_incidenceSet_eq_degree [DecidableEq V] :
    Fintype.card (G.incidenceSet v) = G.degree v := by
  rw [Fintype.card_congr (G.incidenceSetEquivNeighborSet v)]
  simp

@[simp]
theorem card_incidenceFinset_eq_degree [DecidableEq V] : #(G.incidenceFinset v) = G.degree v := by
  rw [← G.card_incidenceSet_eq_degree]
  apply Set.toFinset_card

@[simp]
theorem mem_incidenceFinset [DecidableEq V] (e : Sym2 V) :
    e ∈ G.incidenceFinset v ↔ e ∈ G.incidenceSet v :=
  Set.mem_toFinset

theorem incidenceFinset_eq_filter [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v = {e ∈ G.edgeFinset | v ∈ e} := by
  ext e
  induction e
  simp [mk'_mem_incidenceSet_iff]

end FiniteAt

section LocallyFinite

abbrev LocallyFinite :=
  ∀ v : V, Fintype (G.neighborSet v)

variable [LocallyFinite G]

def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v : V, G.degree v = d

variable {G}

theorem IsRegularOfDegree.degree_eq {d : ℕ} (h : G.IsRegularOfDegree d) (v : V) : G.degree v = d :=
  h v

theorem IsRegularOfDegree.compl [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (h : G.IsRegularOfDegree k) : Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) := by
  intro v
  rw [degree_compl, h v]

end LocallyFinite

section Finite

variable [Fintype V]

instance neighborSetFintype [DecidableRel G.Adj] (v : V) : Fintype (G.neighborSet v) :=
  @Subtype.fintype _ (· ∈ G.neighborSet v)
    (by
      simp_rw [mem_neighborSet]
      infer_instance)
    _

theorem neighborFinset_eq_filter {v : V} [DecidableRel G.Adj] :
    G.neighborFinset v = ({w | G.Adj v w} : Finset _) := by ext; simp

theorem neighborFinset_compl [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    Gᶜ.neighborFinset v = (G.neighborFinset v)ᶜ \ {v} := by
  simp only [neighborFinset, neighborSet_compl, Set.toFinset_diff, Set.toFinset_compl,
    Set.toFinset_singleton]

@[simp]
theorem complete_graph_degree [DecidableEq V] (v : V) :
    (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 := by
  erw [degree, neighborFinset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v), card_univ]

theorem bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0 := by
  erw [degree, neighborFinset_eq_filter, filter_False]
  exact Finset.card_empty

theorem IsRegularOfDegree.top [DecidableEq V] :
    (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
  intro v
  simp

def minDegree [DecidableRel G.Adj] : ℕ :=
  WithTop.untop' 0 (univ.image fun v => G.degree v).min

theorem exists_minimal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.minDegree = G.degree v := by
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image fun v => G.degree v)
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht)
  exact ⟨v, by simp [minDegree, ht]⟩

theorem minDegree_le_degree [DecidableRel G.Adj] (v : V) : G.minDegree ≤ G.degree v := by
  obtain ⟨t, ht⟩ := Finset.min_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.min_le_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [minDegree, ht]

theorem le_minDegree_of_forall_le_degree [DecidableRel G.Adj] [Nonempty V] (k : ℕ)
    (h : ∀ v, k ≤ G.degree v) : k ≤ G.minDegree := by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h

def maxDegree [DecidableRel G.Adj] : ℕ :=
  Option.getD (univ.image fun v => G.degree v).max 0

theorem exists_maximal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.maxDegree = G.degree v := by
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image fun v => G.degree v)
  have ht₂ := mem_of_max ht
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂
  rcases ht₂ with ⟨v, _, rfl⟩
  refine ⟨v, ?_⟩
  rw [maxDegree, ht]
  rfl

theorem degree_le_maxDegree [DecidableRel G.Adj] (v : V) : G.degree v ≤ G.maxDegree := by
  obtain ⟨t, ht : _ = _⟩ := Finset.max_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.le_max_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [maxDegree, ht]

theorem maxDegree_le_of_forall_degree_le [DecidableRel G.Adj] (k : ℕ) (h : ∀ v, G.degree v ≤ k) :
    G.maxDegree ≤ k := by
  by_cases hV : (univ : Finset V).Nonempty
  · haveI : Nonempty V := univ_nonempty_iff.mp hV
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    apply h
  · rw [not_nonempty_iff_eq_empty] at hV
    rw [maxDegree, hV, image_empty]
    exact k.zero_le

theorem degree_lt_card_verts [DecidableRel G.Adj] (v : V) : G.degree v < Fintype.card V := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  exact ⟨v, by simp, Finset.subset_univ _⟩

theorem maxDegree_lt_card_verts [DecidableRel G.Adj] [Nonempty V] :
    G.maxDegree < Fintype.card V := by
  cases' G.exists_maximal_degree_vertex with v hv
  rw [hv]
  apply G.degree_lt_card_verts v

theorem card_commonNeighbors_le_degree_left [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card Set.inter_subset_left

theorem card_commonNeighbors_le_degree_right [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree w := by
  simp_rw [commonNeighbors_symm _ v w, card_commonNeighbors_le_degree_left]

theorem card_commonNeighbors_lt_card_verts [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) < Fintype.card V :=
  Nat.lt_of_le_of_lt (G.card_commonNeighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

theorem Adj.card_commonNeighbors_lt_degree {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V}
    (h : G.Adj v w) : Fintype.card (G.commonNeighbors v w) < G.degree v := by
  classical
  rw [← Set.toFinset_card]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  use w
  constructor
  · rw [Set.mem_toFinset]
    apply not_mem_commonNeighbors_right
  · rw [Finset.insert_subset_iff]
    constructor
    · simpa
    · rw [neighborFinset, Set.toFinset_subset_toFinset]
      exact G.commonNeighbors_subset_neighborSet_left _ _

theorem card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v ≠ w) :
    Fintype.card ((⊤ : SimpleGraph V).commonNeighbors v w) = Fintype.card V - 2 := by
  simp only [commonNeighbors_top_eq, ← Set.toFinset_card, Set.toFinset_diff]
  rw [Finset.card_sdiff]
  · simp [Finset.card_univ, h]
  · simp only [Set.toFinset_subset_toFinset, Set.subset_univ]

end Finite

end SimpleGraph
