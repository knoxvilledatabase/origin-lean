/-
Extracted from Combinatorics/SimpleGraph/VertexCover.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Vertex cover

A *vertex cover* of a simple graph is a set of vertices such that every edge is incident to at least
one of the vertices in the set.

## Main definitions

* `SimpleGraph.IsVertexCover G c`: Predicate that `c` is a vertex cover of `G`.
* `SimpleGraph.vertexCoverNum G`: The vertex cover number, e.g. the size of a minimal vertex cover.
-/

namespace SimpleGraph

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

section IsVertexCover

def IsVertexCover (G : SimpleGraph V) (c : Set V) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → v ∈ c ∨ w ∈ c
