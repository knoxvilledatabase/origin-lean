/-
Extracted from Combinatorics/Digraph/Orientation.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Graph Orientation

This module introduces conversion operations between `Digraph`s and `SimpleGraph`s, by forgetting
the edge orientations of `Digraph`.

## Main Definitions

- `Digraph.toSimpleGraphInclusive`: Converts a `Digraph` to a `SimpleGraph` by creating an
  undirected edge if either orientation exists in the digraph.
- `Digraph.toSimpleGraphStrict`: Converts a `Digraph` to a `SimpleGraph` by creating an undirected
  edge only if both orientations exist in the digraph.

## TODO

- Show that there is an isomorphism between loopless complete digraphs and oriented graphs.
- Define more ways to orient a `SimpleGraph`.
- Provide lemmas on how `toSimpleGraphInclusive` and `toSimpleGraphStrict` relate to other lattice
  structures on `SimpleGraph`s and `Digraph`s.

## Tags

digraph, simple graph, oriented graphs
-/

variable {V : Type*}

namespace Digraph

section toSimpleGraph

/-! ### Orientation-forgetting maps on digraphs -/

def toSimpleGraphInclusive (G : Digraph V) : SimpleGraph V := SimpleGraph.fromRel G.Adj

def toSimpleGraphStrict (G : Digraph V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ G.Adj v w ∧ G.Adj w v
  symm _ _ h := And.intro h.1.symm h.2.symm
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

lemma toSimpleGraphStrict_subgraph_toSimpleGraphInclusive (G : Digraph V) :
    G.toSimpleGraphStrict ≤ G.toSimpleGraphInclusive :=
  fun _ _ h ↦ ⟨h.1, Or.inl h.2.1⟩
