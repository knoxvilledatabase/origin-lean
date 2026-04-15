/-
Extracted from Combinatorics/SimpleGraph/Walk/Traversal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Traversing walks

Functions that help access different parts of a walk.

## Main definitions

* `SimpleGraph.Walk.getVert`:
  Get the nth vertex encountered in a walk, or the last one if `n` is too large
* `SimpleGraph.Walk.snd`: The second vertex of a walk, or the only vertex in an empty walk
* `SimpleGraph.Walk.penultimate`:
  The penultimate vertex of a walk, or the only vertex in an empty walk
* `SimpleGraph.Walk.firstDart`: The first dart of a non-empty walk
* `SimpleGraph.Walk.lastDart`: The last dart of a non-empty walk

## Tags
walks
-/

namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {u v w : V}

def getVert {u v : V} : G.Walk u v → ℕ → V
  | nil, _ => u
  | cons _ _, 0 => u
  | cons _ q, n + 1 => q.getVert n
