/-
Extracted from Combinatorics/SimpleGraph/Walk/Operations.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Operations on walks

Operations on walks that produce a new walk in the same graph.

## Main definitions

* `SimpleGraph.Walk.copy`: Change the endpoints of a walk using equalities
* `SimpleGraph.Walk.append`: Concatenate two compatible walks
* `SimpleGraph.Walk.concat`: Concatenate an edge to the end of a walk
* `SimpleGraph.Walk.reverse`: Reverse a walk
* `SimpleGraph.Walk.drop`: Remove the first `n` darts of a walk
* `SimpleGraph.Walk.take`: Take the first `n` darts of a walk
* `SimpleGraph.Walk.tail`: Remove the first dart of a walk
* `SimpleGraph.Walk.dropLast`: Remove the last dart of a walk

## Tags
walks
-/

open Function

namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {u v w : V}

protected def copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : G.Walk u' v' :=
  hu ▸ hv ▸ p
