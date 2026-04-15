/-
Extracted from Combinatorics/SimpleGraph/Walk/Maps.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Mapping walks between graphs

Functions that map walks between different graphs.

## Main definitions

* `SimpleGraph.Walk.map`: The map on walks induced by a graph homomorphism
* `SimpleGraph.Walk.mapLe`: Map a walk to a supergraph
* `SimpleGraph.Walk.transfer`: Map a walk to another graph that contains its edges
* `SimpleGraph.Walk.induce`:
  Map a walk that's fully contained in a set of vertices to the subgraph induced by that set
* `SimpleGraph.Walk.toDeleteEdges`:
  Map a walk that avoids a set of edges to the subgraph with those edges deleted
* `SimpleGraph.Walk.toDeleteEdge`:
  Map a walk that avoids an edge to the subgraph with that edge deleted

## Tags
walks
-/

namespace SimpleGraph

namespace Walk

universe u v w

variable {V : Type u} {V' : Type v} {V'' : Type w}

variable {G : SimpleGraph V} {G' : SimpleGraph V'} {G'' : SimpleGraph V''}

/-! ### Mapping walks -/

protected def map (f : G →g G') {u v : V} : G.Walk u v → G'.Walk (f u) (f v)
  | nil => nil
  | cons h p => cons (f.map_adj h) (p.map f)

variable (f : G →g G') (f' : G' →g G'') {u v u' v' w : V} (p : G.Walk u v)
