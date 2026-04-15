/-
Extracted from Combinatorics/SimpleGraph/UniversalVerts.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Universal Vertices

This file defines the set of universal vertices: those vertices that are connected
to all others. In addition, it describes results when considering connected components
of the graph where universal vertices are deleted. This particular graph plays a role
in the proof of Tutte's Theorem.

## Main definitions

* `G.universalVerts` is the set of vertices that are connected to all other vertices.
* `G.deleteUniversalVerts` is the subgraph of `G` with the universal vertices removed.
-/

assert_not_exists Field TwoSidedIdeal

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def universalVerts (G : SimpleGraph V) : Set V := {v : V | ∀ ⦃w⦄, v ≠ w → G.Adj w v}

lemma isClique_universalVerts (G : SimpleGraph V) : G.IsClique G.universalVerts :=
  fun _ _ _ hy hxy ↦ hy hxy.symm
