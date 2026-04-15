/-
Extracted from Combinatorics/SimpleGraph/FiveWheelLike.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Five-wheel like graphs

This file defines an `IsFiveWheelLike` structure in a graph, and describes properties of these
structures as well as graphs which avoid this structure. These have two key uses:
* We use them to prove that a maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is
  complete-multipartite: `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree`.
* They play a key role in Brandt's proof of the Andrásfai-Erdős-Sós theorem, which is where they
  first appeared. We give this proof below, see `colorable_of_cliqueFree_lt_minDegree`.

If `G` is maximally `Kᵣ₊₂`-free and `¬ G.Adj x y` (with `x ≠ y`) then there exists an `r`-set `s`
 such that `s ∪ {x}` and `s ∪ {y}` are both `r + 1`-cliques.

If `¬ G.IsCompleteMultipartite` then it contains a `G.IsPathGraph3Compl v w₁ w₂` consisting of
an edge `w₁w₂` and a vertex `v` such that `vw₁` and `vw₂` are non-edges.

Hence any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite must contain distinct
vertices `v, w₁, w₂`, together with `r`-sets `s` and `t`, such that `{v, w₁, w₂}` induces the
single edge `w₁w₂`, `s ∪ t` is disjoint from `{v, w₁, w₂}`, and `s ∪ {v}`, `t ∪ {v}`, `s ∪ {w₁}` and
 `t ∪ {w₂}` are all `r + 1`-cliques.

This leads to the definition of an `IsFiveWheelLike` structure which can be found in any maximally
`Kᵣ₊₂`-free graph that is not complete-multipartite (see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`).

One key parameter in any such structure is the number of vertices common to all of the cliques: we
denote this quantity by `k = #(s ∩ t)` (and we will refer to such a structure as `Wᵣ,ₖ` below.)

The first interesting cases of such structures are `W₁,₀` and `W₂,₁`: `W₁,₀` is a 5-cycle,
while `W₂,₁` is a 5-cycle with an extra central hub vertex adjacent to all other vertices
(i.e. `W₂,₁` resembles a wheel with five spokes).

                 `W₁,₀`       v                 `W₂,₁`      v
                           /     \                       /  |  \
                          s       t                     s ─ u ─ t
                           \     /                       \ / \ /
                           w₁ ─ w₂                       w₁ ─ w₂

## Main definitions

* `SimpleGraph.IsFiveWheelLike`: predicate for `v w₁ w₂ s t` to form a 5-wheel-like subgraph of
  `G` with `r`-sets `s` and `t`, and vertices `v w₁ w₂` forming an `IsPathGraph3Compl` and
  `#(s ∩ t) = k`.

* `SimpleGraph.FiveWheelLikeFree`: predicate for `G` to have no `IsFiveWheelLike r k` subgraph.

## Implementation notes
The definitions of `IsFiveWheelLike` and `IsFiveWheelLikeFree` in this file have `r` shifted by two
compared to the definitions in Brandt **On the structure of graphs with bounded clique number**

The definition of `IsFiveWheelLike` does not contain the facts that `#s = r` and `#t = r` but we
deduce these later as `card_left` and `card_right`.

Although `#(s ∩ t)` can easily be derived from `s` and `t` we include the `IsFiveWheelLike` field
`card_inter : #(s ∩ t) = k` to match the informal / paper definitions and to simplify some
statements of results and match our definition of `IsFiveWheelLikeFree`.

The vertex set of an `IsFiveWheel` structure `Wᵣ,ₖ` is `{v, w₁, w₂} ∪ s ∪ t : Finset α`.
We will need to refer to this consistently and choose the following formulation:
`{v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t)))` which is definitionally equal to
`insert v <| insert w₁ <| insert w₂ <| s ∪ t`.

## References

* [B. Andrásfai, P Erdős, V. T. Sós
  **On the connection between chromatic number, maximal clique, and minimal degree of a graph**
  https://doi.org/10.1016/0012-365X(74)90133-2][andrasfaiErdosSos1974]

* [S. Brandt **On the structure of graphs with bounded clique number**
  https://doi.org/10.1007/s00493-003-0042-z][brandt2003]
-/

local notation "‖" x "‖" => Fintype.card x

open Finset SimpleGraph

variable {α : Type*} {a b c : α} {s : Finset α} {G : SimpleGraph α} {r k : ℕ}

namespace SimpleGraph

section withDecEq

variable [DecidableEq α]

private lemma IsNClique.insert_insert (h1 : G.IsNClique r (insert a s))
    (h2 : G.IsNClique r (insert b s)) (h3 : b ∉ s) (ha : G.Adj a b) :
    G.IsNClique (r + 1) (insert b (insert a s)) := by
  apply h1.insert (fun b hb ↦ ?_)
  obtain (rfl | h) := mem_insert.1 hb
  · exact ha.symm
  · exact h2.1 (mem_insert_self _ s) (mem_insert_of_mem h) <| fun h' ↦ (h3 (h' ▸ h)).elim

private lemma IsNClique.insert_insert_erase (hs : G.IsNClique r (insert a s)) (hc : c ∈ s)
    (ha : a ∉ s) (hd : ∀ w ∈ insert a s, w ≠ c → G.Adj w b) :
    G.IsNClique r (insert a (insert b (erase s c))) := by
  rw [insert_comm, ← erase_insert_of_ne (fun h : a = c ↦ ha (h ▸ hc) |>.elim)]
  simp_rw [adj_comm, ← notMem_singleton] at hd
  exact hs.insert_erase (fun _ h ↦ hd _ (mem_sdiff.1 h).1 (mem_sdiff.1 h).2) (mem_insert_of_mem hc)
