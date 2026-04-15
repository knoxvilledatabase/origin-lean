/-
Extracted from Combinatorics/SimpleGraph/Matching.lean
Genuine: 14 of 16 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Matchings

A *matching* for a simple graph is a set of disjoint pairs of adjacent vertices, and the set of all
the vertices in a matching is called its *support* (and sometimes the vertices in the support are
said to be *saturated* by the matching). A *perfect matching* is a matching whose support contains
every vertex of the graph.

In this module, we represent a matching as a subgraph whose vertices are each incident to at most
one edge, and the edges of the subgraph represent the paired vertices.

## Main definitions

* `SimpleGraph.Subgraph.IsMatching`: `M.IsMatching` means that `M` is a matching of its
  underlying graph.

* `SimpleGraph.Subgraph.IsPerfectMatching` defines when a subgraph `M` of a simple graph is a
  perfect matching, denoted `M.IsPerfectMatching`.

* `SimpleGraph.IsMatchingFree` means that a graph `G` has no perfect matchings.

* `SimpleGraph.IsCycles` means that a graph consists of cycles (including cycles of length 0,
  also known as isolated vertices)

* `SimpleGraph.IsAlternating` means that edges in a graph `G` are alternatingly
  included and not included in some other graph `G'`

## TODO

* Define an `other` function and prove useful results about it (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/266205863)

* Provide a bicoloring for matchings (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/265495120)

* Tutte's Theorem
-/

assert_not_exists Field TwoSidedIdeal

open Function

namespace SimpleGraph

variable {V W : Type*} {G G' : SimpleGraph V} {M M' : Subgraph G} {u v w : V}

namespace Subgraph

def IsMatching (M : Subgraph G) : Prop := ∀ ⦃v⦄, v ∈ M.verts → ∃! w, M.Adj v w

noncomputable def IsMatching.toEdge (h : M.IsMatching) (v : M.verts) : M.edgeSet :=
  ⟨s(v, (h v.property).choose), (h v.property).choose_spec.1⟩

theorem IsMatching.toEdge_eq_of_adj (h : M.IsMatching) (hv : v ∈ M.verts) (hvw : M.Adj v w) :
    h.toEdge ⟨v, hv⟩ = ⟨s(v, w), hvw⟩ := by
  simp only [IsMatching.toEdge, Subtype.mk_eq_mk]
  congr
  exact ((h (M.edge_vert hvw)).choose_spec.2 w hvw).symm

theorem IsMatching.toEdge.surjective (h : M.IsMatching) : Surjective h.toEdge := by
  rintro ⟨⟨x, y⟩, he⟩
  exact ⟨⟨x, M.edge_vert he⟩, h.toEdge_eq_of_adj _ he⟩

theorem IsMatching.toEdge_eq_toEdge_of_adj (h : M.IsMatching)
    (hv : v ∈ M.verts) (hw : w ∈ M.verts) (ha : M.Adj v w) :
    h.toEdge ⟨v, hv⟩ = h.toEdge ⟨w, hw⟩ := by
  rw [h.toEdge_eq_of_adj hv ha, h.toEdge_eq_of_adj hw (M.symm ha), Subtype.mk_eq_mk, Sym2.eq_swap]

lemma IsMatching.eq_of_adj_left (hM : M.IsMatching) (huv : M.Adj u v) (huw : M.Adj u w) : v = w :=
  (hM <| M.edge_vert huv).unique huv huw

lemma IsMatching.eq_of_adj_right (hM : M.IsMatching) (huw : M.Adj u w) (hvw : M.Adj v w) : u = v :=
  hM.eq_of_adj_left huw.symm hvw.symm

lemma IsMatching.not_adj_left_of_ne (hM : M.IsMatching) (hvw : v ≠ w) (huv : M.Adj u v) :
    ¬M.Adj u w := fun huw ↦ hvw <| hM.eq_of_adj_left huv huw

lemma IsMatching.not_adj_right_of_ne (hM : M.IsMatching) (huv : u ≠ v) (huw : M.Adj u w) :
    ¬M.Adj v w := fun hvw ↦ huv <| hM.eq_of_adj_right huw hvw

lemma IsMatching.sup (hM : M.IsMatching) (hM' : M'.IsMatching)
    (hd : Disjoint M.support M'.support) : (M ⊔ M').IsMatching := by
  intro v hv
  have aux {N N' : Subgraph G} (hN : N.IsMatching) (hd : Disjoint N.support N'.support)
    (hmN : v ∈ N.verts) : ∃! w, (N ⊔ N').Adj v w := by
    obtain ⟨w, hw⟩ := hN hmN
    use w
    refine ⟨sup_adj.mpr (.inl hw.1), ?_⟩
    intro y hy
    cases hy with
    | inl h => exact hw.2 y h
    | inr h =>
      rw [Set.disjoint_left] at hd
      simpa [(mem_support _).mpr ⟨w, hw.1⟩, (mem_support _).mpr ⟨y, h⟩] using @hd v
  cases Set.mem_or_mem_of_mem_union hv with
  | inl hmM => exact aux hM hd hmM
  | inr hmM' =>
    rw [sup_comm]
    exact aux hM' (Disjoint.symm hd) hmM'

lemma IsMatching.iSup {ι : Sort _} {f : ι → Subgraph G} (hM : (i : ι) → (f i).IsMatching)
    (hd : Pairwise fun i j ↦ Disjoint (f i).support (f j).support) :
    (⨆ i, f i).IsMatching := by
  intro v hv
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (verts_iSup ▸ hv)
  obtain ⟨w, hw⟩ := hM i hi
  use w
  refine ⟨iSup_adj.mpr ⟨i, hw.1⟩, ?_⟩
  intro y hy
  obtain ⟨i', hi'⟩ := iSup_adj.mp hy
  by_cases heq : i = i'
  · exact hw.2 y (heq.symm ▸ hi')
  · have := hd heq
    simp only [Set.disjoint_left] at this
    simpa [(mem_support _).mpr ⟨w, hw.1⟩, (mem_support _).mpr ⟨y, hi'⟩] using @this v

lemma IsMatching.subgraphOfAdj (h : G.Adj v w) : (G.subgraphOfAdj h).IsMatching := by
  intro _ hv
  rw [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  cases hv with
  | inl => use w; aesop
  | inr => use v; aesop

lemma IsMatching.coeSubgraph {G' : Subgraph G} {M : Subgraph G'.coe} (hM : M.IsMatching) :
    (Subgraph.coeSubgraph M).IsMatching := by
  intro _ hv
  obtain ⟨w, hw⟩ := hM <| Set.mem_of_mem_image_val <| (Subgraph.verts_coeSubgraph M).symm ▸ hv
  use w
  refine ⟨?_, fun y hy => ?_⟩
  · obtain ⟨v, hv⟩ := (Set.mem_image _ _ _).mp <| (Subgraph.verts_coeSubgraph M).symm ▸ hv
    simp only [coeSubgraph_adj, Subtype.coe_eta, Subtype.coe_prop, exists_const]
    exact ⟨hv.2 ▸ v.2, hw.1⟩
  · obtain ⟨_, hw', hvw⟩ := (coeSubgraph_adj _ _ _).mp hy
    rw [← hw.2 ⟨y, hw'⟩ hvw]

protected lemma IsMatching.map {G' : SimpleGraph W} {M : Subgraph G} (f : G →g G')
    (hf : Injective f) (hM : M.IsMatching) : (M.map f).IsMatching := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨v', hv'⟩ := hM hv
  use f v'
  refine ⟨⟨v, v', hv'.1, rfl, rfl⟩, ?_⟩
  rintro _ ⟨w, w', hw, hw', rfl⟩
  cases hf hw'.symm
  rw [hv'.2 w' hw]
