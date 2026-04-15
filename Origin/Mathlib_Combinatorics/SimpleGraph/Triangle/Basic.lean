/-
Extracted from Combinatorics/SimpleGraph/Triangle/Basic.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Triangles in graphs

A *triangle* in a simple graph is a `3`-clique, namely a set of three vertices that are
pairwise adjacent.

This module defines and proves properties about triangles in simple graphs.

## Main declarations

* `SimpleGraph.FarFromTriangleFree`: Predicate for a graph such that one must remove a lot of edges
  from it for it to become triangle-free. This is the crux of the Triangle Removal Lemma.

## TODO

* Generalise `FarFromTriangleFree` to other graphs, to state and prove the Graph Removal Lemma.
-/

open Finset Nat

open Fintype (card)

namespace SimpleGraph

variable {α β 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {G H : SimpleGraph α} {ε δ : 𝕜}

section LocallyLinear

def EdgeDisjointTriangles (G : SimpleGraph α) : Prop :=
  (G.cliqueSet 3).Pairwise fun x y ↦ (x ∩ y : Set α).Subsingleton

def LocallyLinear (G : SimpleGraph α) : Prop :=
  G.EdgeDisjointTriangles ∧ ∀ ⦃x y⦄, G.Adj x y → ∃ s, G.IsNClique 3 s ∧ x ∈ s ∧ y ∈ s

protected lemma LocallyLinear.edgeDisjointTriangles : G.LocallyLinear → G.EdgeDisjointTriangles :=
  And.left

nonrec lemma EdgeDisjointTriangles.mono (h : G ≤ H) (hH : H.EdgeDisjointTriangles) :
    G.EdgeDisjointTriangles := hH.mono <| cliqueSet_mono h
