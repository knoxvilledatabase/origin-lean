/-
Extracted from Combinatorics/SimpleGraph/Walk/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Walks

In a simple graph, a *walk* is a finite sequence of adjacent vertices, and can be
thought of equally well as a sequence of directed edges.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk` (with accompanying pattern definitions
  `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'`)
* `SimpleGraph.Walk.Nil`: A predicate for the empty walk
* `SimpleGraph.Walk.length`: The length of a walk
* `SimpleGraph.Walk.support`: The list of vertices a walk visits in order
* `SimpleGraph.Walk.darts`: The list of darts a walk visits in order
* `SimpleGraph.Walk.edges`: The list of edges a walk visits in order
* `SimpleGraph.Walk.edgeSet`: The set of edges of a walk visits

## Tags
walks
-/

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V) {u v w : V}

inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq

attribute [refl] Walk.nil
