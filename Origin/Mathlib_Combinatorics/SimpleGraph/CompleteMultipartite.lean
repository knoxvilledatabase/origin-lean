/-
Extracted from Combinatorics/SimpleGraph/CompleteMultipartite.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Complete Multipartite Graphs

A graph is complete multipartite iff non-adjacency is transitive.

## Main declarations

* `SimpleGraph.IsCompleteMultipartite`: predicate for a graph to be complete multipartite.

* `SimpleGraph.IsCompleteMultipartite.setoid`: the `Setoid` given by non-adjacency.

* `SimpleGraph.IsCompleteMultipartite.iso`: the graph isomorphism from a graph that
  `IsCompleteMultipartite` to the corresponding `completeMultipartiteGraph`.

* `SimpleGraph.IsPathGraph3Compl`: predicate for three vertices to witness the
  non-complete-multipartiteness of a graph `G`. (The name refers to the fact that the three
  vertices form the complement of `pathGraph 3`.)

* See also: `Mathlib/Combinatorics/SimpleGraph/FiveWheelLike.lean`.
  The lemma `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree` states that a maximally
  `r + 1`-cliquefree graph is `r`-colorable iff it is complete multipartite.

* `SimpleGraph.completeEquipartiteGraph`: the **complete equipartite graph** in parts of *equal*
  size such that two vertices are adjacent if and only if they are in different parts.

* `SimpleGraph.CompleteEquipartiteSubgraph G r t` is a complete equipartite subgraph, that is,
  `r` subsets of vertices each of size `t` such that the vertices in distinct subsets are
  adjacent.

## Implementation Notes

The definition of `completeEquipartiteGraph` is similar to `completeMultipartiteGraph`
except that `Sigma.fst` is replaced by `Prod.fst` in the definition. The difference is that the
former vertices are a product type whereas the latter vertices are a *dependent* product type.

While `completeEquipartiteGraph r t` could have been defined as the specialisation
`completeMultipartiteGraph (const (Fin r) (Fin t))` (or `turanGraph (r * t) r`), it is convenient
to instead have a *non-dependent* *product* type for the vertices.

See `completeEquipartiteGraph.completeMultipartiteGraph`, `completeEquipartiteGraph.turanGraph`
for the isomorphisms between a `completeEquipartiteGraph` and a corresponding
`completeMultipartiteGraph`, `turanGraph`.
-/

open Finset Fintype Function

universe u

namespace SimpleGraph

variable {α : Type u} {G : SimpleGraph α} {s : Set α}

def IsCompleteMultipartite (G : SimpleGraph α) : Prop := IsTrans α (¬ G.Adj · ·)

theorem bot_isCompleteMultipartite : (⊥ : SimpleGraph α).IsCompleteMultipartite :=
  ⟨by simp⟩

protected lemma IsCompleteMultipartite.induce (hG : G.IsCompleteMultipartite) :
    (G.induce s).IsCompleteMultipartite where trans _u _v _w := hG.trans _ _ _
