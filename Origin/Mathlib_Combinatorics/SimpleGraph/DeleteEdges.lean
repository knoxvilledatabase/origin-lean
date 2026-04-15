/-
Extracted from Combinatorics/SimpleGraph/DeleteEdges.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Edge deletion

This file defines operations deleting the edges of a simple graph and proves theorems in the finite
case.

## Main definitions

* `SimpleGraph.deleteEdges G s` is the simple graph `G` with the edges `s : Set (Sym2 V)` removed
  from the edge set.

* `SimpleGraph.deleteIncidenceSet G v` is the simple graph `G` with the incidence set of `v`
  removed from the edge set.

* `SimpleGraph.deleteFar G p r` is the predicate that a graph is `r`-*delete-far* from a property
  `p`, that is, at least `r` edges must be deleted to satisfy `p`.
-/

open Finset Fintype

namespace SimpleGraph

variable {V : Type*} {v w : V} (G : SimpleGraph V)

section DeleteEdges

def deleteEdges (s : Set (Sym2 V)) : SimpleGraph V := G \ fromEdgeSet s

variable {G} {H : SimpleGraph V} {s s₁ s₂ : Set (Sym2 V)}

-- INSTANCE (free from Core): [DecidableRel
