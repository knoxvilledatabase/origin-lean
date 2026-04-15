/-
Extracted from Combinatorics/SimpleGraph/Operations.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Local graph operations

This file defines some single-graph operations that modify a finite number of vertices
and proves basic theorems about them. When the graph itself has a finite number of vertices
we also prove theorems about the number of edges in the modified graphs.

## Main definitions

* `G.replaceVertex s t` is `G` with `t` replaced by a copy of `s`,
  removing the `s-t` edge if present.
* `edge s t` is the graph with a single `s-t` edge. Adding this edge to a graph `G` is then
  `G ⊔ edge s t`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (s t : V)

section ReplaceVertex

variable [DecidableEq V]

def replaceVertex : SimpleGraph V where
  Adj v w := if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  symm v w := by dsimp only; split_ifs <;> simp [adj_comm]

lemma not_adj_replaceVertex_same : ¬(G.replaceVertex s t).Adj s t := by simp [replaceVertex]
