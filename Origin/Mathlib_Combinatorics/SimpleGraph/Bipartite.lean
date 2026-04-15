/-
Extracted from Combinatorics/SimpleGraph/Bipartite.lean
Genuine: 45 of 52 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Bipartite graphs

This file proves results about bipartite simple graphs, including several double-counting arguments.

## Main definitions

* `SimpleGraph.IsBipartiteWith G s t` is the condition that a simple graph `G` is bipartite in sets
  `s`, `t`, that is, `s` and `t` are disjoint and vertices `v`, `w` being adjacent in `G` implies
  that `v ∈ s` and `w ∈ t`, or `v ∈ t` and `w ∈ s`.

  Note that in this implementation, if `G.IsBipartiteWith s t`, `s ∪ t` need not cover the vertices
  of `G`, instead `s ∪ t` is only required to cover the *support* of `G`, that is, the vertices
  that form edges in `G`. This definition is equivalent to the expected definition. If `s` and `t`
  do not cover all the vertices, one recovers a covering of all the vertices by unioning the
  missing vertices `(s ∪ t)ᶜ` to either `s` or `t`.

* `SimpleGraph.IsBipartite`: Predicate for a simple graph to be bipartite.
  `G.IsBipartite` is defined as an abbreviation for `G.Colorable 2`.

* `SimpleGraph.isBipartite_iff_exists_isBipartiteWith` is the proof that `G.IsBipartite` iff
  `G.IsBipartiteWith s t`.

* `SimpleGraph.isBipartiteWith_sum_degrees_eq` is the proof that if `G.IsBipartiteWith s t`, then
  the sum of the degrees of the vertices in `s` is equal to the sum of the degrees of the vertices
  in `t`.

* `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges` is the proof that if
  `G.IsBipartiteWith s t`, then sum of the degrees of the vertices in `s` is equal to the number of
  edges in `G`.

  See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
  `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'` for the version from the "right".

* `SimpleGraph.completeBipartiteGraph_isContained_iff` is the proof that simple graphs contain a
  copy of a `completeBipartiteGraph α β` iff there exists a "left" subset of `card α` vertices and
  a "right" subset of `card β` vertices such that every vertex in the "left" subset is adjacent to
  every vertex in the "right" subset.

* `SimpleGraph.between`; the simple graph `G.between s t` is the subgraph of `G` containing edges
  that connect a vertex in the set `s` to a vertex in the set `t`.

* `SimpleGraph.bipartiteDoubleCover`; the simple graph `G.bipartiteDoubleCover` has two vertices
  `inl v` and `inr v` for each vertex `v` in `G` such that `inl v` (`inr v`) is adjacent to `inr w`
  (`inl w`) iff `v` is adjacent to `w` in `G`.

## Implementation notes

For the formulation of double-counting arguments where a bipartite graph is considered as a
relation `r : α → β → Prop`, see `Mathlib/Combinatorics/Enumerative/DoubleCounting.lean`.

## TODO

* Prove that `G.IsBipartite` iff `G` does not contain an odd cycle.
  I.e., `G.IsBipartite ↔ ∀ n, (cycleGraph (2*n+1)).Free G`.
-/

open Finset Fintype

namespace SimpleGraph

variable {V : Type*} {v w : V} {G : SimpleGraph V} {s t : Set V}

section IsBipartiteWith

structure IsBipartiteWith (G : SimpleGraph V) (s t : Set V) : Prop where
  disjoint : Disjoint s t
  mem_of_adj ⦃v w : V⦄ : G.Adj v w → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s

theorem isBipartiteWith_comm : G.IsBipartiteWith s t ↔ G.IsBipartiteWith t s :=
  ⟨IsBipartiteWith.symm, IsBipartiteWith.symm⟩

theorem IsBipartiteWith.mem_of_mem_adj
    (h : G.IsBipartiteWith s t) (hv : v ∈ s) (hadj : G.Adj v w) : w ∈ t := by
  apply h.mem_of_adj at hadj
  have nhv : v ∉ t := Set.disjoint_left.mp h.disjoint hv
  simpa [hv, nhv] using hadj

theorem isBipartiteWith_neighborSet (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborSet v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborSet, Set.mem_setOf_eq, iff_and_self]
  exact h.mem_of_mem_adj hv

theorem isBipartiteWith_neighborSet_subset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborSet v ⊆ t := by
  rw [isBipartiteWith_neighborSet h hv]
  exact Set.sep_subset t (G.Adj v ·)

theorem isBipartiteWith_neighborSet_disjoint (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    Disjoint (G.neighborSet v) s :=
  Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset h hv) h.disjoint.symm

theorem IsBipartiteWith.mem_of_mem_adj'
    (h : G.IsBipartiteWith s t) (hw : w ∈ t) (hadj : G.Adj v w) : v ∈ s := by
  apply h.mem_of_adj at hadj
  have nhw : w ∉ s := Set.disjoint_right.mp h.disjoint hw
  simpa [hw, nhw] using hadj

theorem isBipartiteWith_neighborSet' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborSet w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborSet, adj_comm, Set.mem_setOf_eq, iff_and_self]
  exact h.mem_of_mem_adj' hw

theorem isBipartiteWith_neighborSet_subset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborSet w ⊆ s := by
  rw [isBipartiteWith_neighborSet' h hw]
  exact Set.sep_subset s (G.Adj · w)

theorem isBipartiteWith_support_subset (h : G.IsBipartiteWith s t) : G.support ⊆ s ∪ t := by
  intro v ⟨w, hadj⟩
  apply h.mem_of_adj at hadj
  tauto

theorem isBipartiteWith_neighborSet_disjoint' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    Disjoint (G.neighborSet w) t :=
  Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset' h hw) h.disjoint

variable {s t : Finset V}

variable [Fintype ↑(G.neighborSet v)] [Fintype ↑(G.neighborSet w)]

section decidableRel

variable [DecidableRel G.Adj]

theorem isBipartiteWith_neighborFinset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborFinset, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj hv

theorem isBipartiteWith_neighborFinset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborFinset, adj_comm, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj' hw

theorem isBipartiteWith_bipartiteAbove (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = bipartiteAbove G.Adj t v := by
  rw [isBipartiteWith_neighborFinset h hv, bipartiteAbove]

theorem isBipartiteWith_bipartiteBelow (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = bipartiteBelow G.Adj s w := by
  rw [isBipartiteWith_neighborFinset' h hw, bipartiteBelow]

end decidableRel

theorem isBipartiteWith_neighborFinset_subset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v ⊆ t := by
  classical
  rw [isBipartiteWith_neighborFinset h hv]
  exact filter_subset (G.Adj v ·) t

theorem isBipartiteWith_neighborFinset_disjoint (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    Disjoint (G.neighborFinset v) s := by
  rw [neighborFinset_def, ← disjoint_coe, Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint h hv

theorem isBipartiteWith_degree_le (h : G.IsBipartiteWith s t) (hv : v ∈ s) : G.degree v ≤ #t := by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset h hv)

theorem isBipartiteWith_neighborFinset_subset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w ⊆ s := by
  classical
  rw [isBipartiteWith_neighborFinset' h hw]
  exact filter_subset (G.Adj · w) s

theorem isBipartiteWith_neighborFinset_disjoint' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    Disjoint (G.neighborFinset w) t := by
  rw [neighborFinset_def, ← disjoint_coe, Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint' h hw

theorem isBipartiteWith_degree_le' (h : G.IsBipartiteWith s t) (hw : w ∈ t) : G.degree w ≤ #s := by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset' h hw)

end

theorem isBipartiteWith_sum_degrees_eq [G.LocallyFinite] (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s, G.degree v = ∑ w ∈ t, G.degree w := by
  classical
  simp_rw [← sum_attach t, ← sum_attach s, ← card_neighborFinset_eq_degree]
  conv_lhs =>
    rhs; intro v
    rw [isBipartiteWith_bipartiteAbove h v.prop]
  conv_rhs =>
    rhs; intro w
    rw [isBipartiteWith_bipartiteBelow h w.prop]
  simp_rw [sum_attach s fun w ↦ #(bipartiteAbove G.Adj t w),
    sum_attach t fun v ↦ #(bipartiteBelow G.Adj s v)]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj

variable [Fintype V] [DecidableRel G.Adj]

lemma isBipartiteWith_sum_degrees_eq_twice_card_edges [DecidableEq V] (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s ∪ t, G.degree v = 2 * #G.edgeFinset := by
  have hsub : G.support ⊆ ↑s ∪ ↑t := isBipartiteWith_support_subset h
  rw [← coe_union, ← Set.toFinset_subset] at hsub
  rw [← Finset.sum_subset hsub, ← sum_degrees_support_eq_twice_card_edges]
  intro v _ hv
  rwa [Set.mem_toFinset, ← degree_eq_zero_iff_notMem_support] at hv

theorem isBipartiteWith_sum_degrees_eq_card_edges (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s, G.degree v = #G.edgeFinset := by
  classical
  rw [← Nat.mul_left_cancel_iff zero_lt_two, ← isBipartiteWith_sum_degrees_eq_twice_card_edges h,
    sum_union (disjoint_coe.mp h.disjoint), two_mul, add_right_inj]
  exact isBipartiteWith_sum_degrees_eq h

theorem isBipartiteWith_sum_degrees_eq_card_edges' (h : G.IsBipartiteWith s t) :
    ∑ v ∈ t, G.degree v = #G.edgeFinset := isBipartiteWith_sum_degrees_eq_card_edges h.symm

end IsBipartiteWith

section IsBipartite

abbrev IsBipartite (G : SimpleGraph V) : Prop := G.Colorable 2

theorem isBipartite_iff_exists_isBipartiteWith :
    G.IsBipartite ↔ ∃ s t : Set V, G.IsBipartiteWith s t :=
  ⟨IsBipartite.exists_isBipartiteWith, fun ⟨_, _, h⟩ ↦ h.isBipartite⟩

end IsBipartite

section Copy

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def Copy.completeBipartiteGraph
    (left right : Finset V) (card_left : #left = card α) (card_right : #right = card β)
    (h : G.IsCompleteBetween left right) : Copy (completeBipartiteGraph α β) G := by
  have : Nonempty (α ↪ left) := by
    rw [← card_coe] at card_left
    exact Function.Embedding.nonempty_of_card_le card_left.symm.le
  let fα : α ↪ left := Classical.arbitrary (α ↪ left)
  have : Nonempty (β ↪ right) := by
    rw [← card_coe] at card_right
    exact Function.Embedding.nonempty_of_card_le card_right.symm.le
  let fβ : β ↪ right := Classical.arbitrary (β ↪ right)
  let f : α ⊕ β ↪ V := by
    refine ⟨Sum.elim (Subtype.val ∘ fα) (Subtype.val ∘ fβ), fun s₁ s₂ ↦ ?_⟩
    match s₁, s₂ with
    | .inl p₁, .inl p₂ => simp
    | .inr p₁, .inl p₂ =>
      simpa using (h (fα p₂).prop (fβ p₁).prop).ne'
    | .inl p₁, .inr p₂ =>
      simpa using (h (fα p₁).prop (fβ p₂).prop).symm.ne'
    | .inr p₁, .inr p₂ => simp
  refine ⟨⟨f.toFun, fun {s₁ s₂} hadj ↦ ?_⟩, f.injective⟩
  rcases hadj with ⟨hs₁, hs₂⟩ | ⟨hs₁, hs₂⟩
  all_goals dsimp [f]
  · rw [← Sum.inl_getLeft s₁ hs₁, ← Sum.inr_getRight s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr]
    exact h (by simp) (by simp)
  · rw [← Sum.inr_getRight s₁ hs₁, ← Sum.inl_getLeft s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr, adj_comm]
    exact h (by simp) (by simp)

theorem completeBipartiteGraph_isContained_iff :
    completeBipartiteGraph α β ⊑ G ↔
      ∃ (left right : Finset V), #left = card α ∧ #right = card β
        ∧ G.IsCompleteBetween left right where
  mp := by
    refine fun ⟨f⟩ ↦ ⟨univ.map ⟨f ∘ Sum.inl, f.injective.comp Sum.inl_injective⟩,
      univ.map ⟨f ∘ Sum.inr, f.injective.comp Sum.inr_injective⟩, by simp, by simp,
      fun _ hl _ hr ↦ ?_⟩
    rw [mem_coe, mem_map] at hl hr
    replace ⟨_, _, hl⟩ := hl
    replace ⟨_, _, hr⟩ := hr
    rw [← hl, ← hr]
    exact f.toHom.map_adj (by simp)
  mpr := fun ⟨left, right, card_left, card_right, h⟩ ↦
    ⟨.completeBipartiteGraph left right card_left card_right h⟩

end Copy

lemma IsBipartiteWith.subgraph (h : G.IsBipartiteWith s t) (H : Subgraph G) :
    H.coe.IsBipartiteWith {x : H.verts | ↑x ∈ s} {x : H.verts | ↑x ∈ t} :=
  ⟨by grind [h.disjoint], fun _ _ hadj' ↦ h.mem_of_adj <| H.adj_sub hadj'⟩

lemma IsBipartite.subgraph (h : G.IsBipartite) (H : Subgraph G) : H.coe.IsBipartite :=
  let ⟨_, _, hst⟩ := isBipartite_iff_exists_isBipartiteWith.mp h
  isBipartite_iff_exists_isBipartiteWith.mpr ⟨_, _, IsBipartiteWith.subgraph hst H⟩

section Between

def between (s t : Set V) (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s)
  symm v w := by tauto

lemma between_le : G.between s t ≤ G := fun _ _ h ↦ h.1

lemma between_comm : G.between s t = G.between t s := by simp [between, or_comm]

-- INSTANCE (free from Core): [DecidableRel

theorem between_isBipartite (h : Disjoint s t) : (G.between s t).IsBipartite :=
  (between_isBipartiteWith h).isBipartite

lemma neighborSet_subset_between_union (hv : v ∈ s) :
    G.neighborSet v ⊆ (G.between s sᶜ).neighborSet v ∪ s := by
  intro w hadj
  rw [neighborSet, Set.mem_union, Set.mem_setOf, between_adj]
  by_cases hw : w ∈ s
  · exact Or.inr hw
  · exact Or.inl ⟨hadj, Or.inl ⟨hv, hw⟩⟩

lemma neighborSet_subset_between_union_compl (hw : w ∈ sᶜ) :
    G.neighborSet w ⊆ (G.between s sᶜ).neighborSet w ∪ sᶜ := by
  intro v hadj
  rw [neighborSet, Set.mem_union, Set.mem_setOf, between_adj]
  by_cases hv : v ∈ s
  · exact Or.inl ⟨hadj, Or.inr ⟨hw, hv⟩⟩
  · exact Or.inr hv

variable [DecidableEq V] [Fintype V] {s t : Finset V} [DecidableRel G.Adj]

lemma neighborFinset_subset_between_union (hv : v ∈ s) :
    G.neighborFinset v ⊆ (G.between s sᶜ).neighborFinset v ∪ s := by
  simpa [neighborFinset_def] using neighborSet_subset_between_union hv

theorem degree_le_between_add (hv : v ∈ s) :
    G.degree v ≤ (G.between s sᶜ).degree v + s.card := by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint h_bipartite hv)]
  exact card_le_card (neighborFinset_subset_between_union hv)

lemma neighborFinset_subset_between_union_compl (hw : w ∈ sᶜ) :
    G.neighborFinset w ⊆ (G.between s sᶜ).neighborFinset w ∪ sᶜ := by
  simpa [neighborFinset_def] using G.neighborSet_subset_between_union_compl (by simpa using hw)

theorem degree_le_between_add_compl (hw : w ∈ sᶜ) :
    G.degree w ≤ (G.between s sᶜ).degree w + sᶜ.card := by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint' h_bipartite hw)]
  exact card_le_card (neighborFinset_subset_between_union_compl hw)

end Between

section completeBipartiteGraph

variable {W₁ W₂ : Type*}

theorem edgeSet_completeBipartiteGraph :
    (completeBipartiteGraph W₁ W₂).edgeSet =
    .range (fun x : W₁ × W₂ ↦ s(.inl x.1, .inr x.2)) := by
  refine Set.ext <| Sym2.ind fun u v ↦ ⟨fun h ↦ ?_, fun ⟨⟨a, b⟩, z⟩ ↦ ?_⟩
  · cases u <;> cases v <;> simp_all
  · grind [completeBipartiteGraph_adj, mem_edgeSet]

theorem encard_edgeSet_completeBipartiteGraph :
    (completeBipartiteGraph W₁ W₂).edgeSet.encard = ENat.card W₁ * ENat.card W₂ := by
  rw [edgeSet_completeBipartiteGraph, ← ENat.card_prod, ← Set.encard_univ, ← Set.image_univ]
  exact Function.Injective.encard_image (by grind [Function.Injective]) Set.univ

def IsBipartiteWith.edgeSetEmbeddingCompleteBipartiteGraph [DecidableRel (· ∈ · : V → Set V → _)]
    (hG : G.IsBipartiteWith s t) : G.edgeSet ↪ (completeBipartiteGraph s t).edgeSet where
  toFun := fun ⟨e, he⟩ ↦
    e.hrec (fun u v h ↦ hG.mem_of_adj h |>.by_cases
      (fun h ↦ ⟨s(.inl ⟨u, h.left⟩, .inr ⟨v, h.right⟩), .inl ⟨rfl, rfl⟩⟩)
      (fun h ↦ ⟨s(.inl ⟨v, h.right⟩, .inr ⟨u, h.left⟩), .inl ⟨rfl, rfl⟩⟩)
    ) (fun _ _ ↦ Function.hfunext (by grind) <| by grind [Or.by_cases, hG.disjoint]) he
  inj' := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    change (if _ : _ then _ else _) = (if _ : _ then _ else _) → _
    grind

end completeBipartiteGraph

theorem IsBipartiteWith.encard_edgeSet_le (hG : G.IsBipartiteWith s t) :
    G.edgeSet.encard ≤ s.encard * t.encard := by
  classical
  grw [hG.edgeSetEmbeddingCompleteBipartiteGraph.encard_le]
  simp [encard_edgeSet_completeBipartiteGraph]

end

section BipartiteDoubleCover
