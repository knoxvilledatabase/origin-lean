/-
Extracted from Combinatorics/SimpleGraph/Maps.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Maps between graphs

This file defines two functions and three structures relating graphs.
The structures directly correspond to the classification of functions as
injective, surjective and bijective, and have corresponding notation.

## Main definitions

* `SimpleGraph.map`: the graph obtained by pushing the adjacency relation through
  an injective function between vertex types.
* `SimpleGraph.comap`: the graph obtained by pulling the adjacency relation behind
  an arbitrary function between vertex types.
* `SimpleGraph.induce`: the subgraph induced by the given vertex set, a wrapper around `comap`.
* `SimpleGraph.spanningCoe`: the supergraph without any additional edges, a wrapper around `map`.
* `SimpleGraph.Hom`, `G →g H`: a graph homomorphism from `G` to `H`.
* `SimpleGraph.Embedding`, `G ↪g H`: a graph embedding of `G` in `H`.
* `SimpleGraph.Iso`, `G ≃g H`: a graph isomorphism between `G` and `H`.

Note that a graph embedding is a stronger notion than an injective graph homomorphism,
since its image is an induced subgraph.

## Implementation notes

Morphisms of graphs are abbreviations for `RelHom`, `RelEmbedding` and `RelIso`.
To make use of pre-existing simp lemmas, definitions involving morphisms are
abbreviations as well.
-/

open Function

namespace SimpleGraph

variable {V W X : Type*} (G : SimpleGraph V) (G' : SimpleGraph W) {u v : V}

/-! ## Map and comap -/

protected def map (f : V → W) (G : SimpleGraph V) : SimpleGraph W where
  Adj := Ne ⊓ Relation.Map G.Adj f f
  symm a b := by
    rintro ⟨v, w, h, _⟩
    aesop (add norm unfold Relation.Map) (add forward safe Adj.symm)

-- INSTANCE (free from Core): instDecidableMapAdj
