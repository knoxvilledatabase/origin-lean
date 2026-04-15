/-
Extracted from Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Edge Connectivity

This file defines k-edge-connectivity for simple graphs.

## Main definitions

* `SimpleGraph.IsEdgeReachable`: Two vertices are `k`-edge-reachable if they remain reachable after
  removing strictly fewer than `k` edges.
* `SimpleGraph.IsEdgeConnected`: A graph is `k`-edge-connected if any two vertices are
  `k`-edge-reachable.
-/

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ} {u v w x y : V}

variable (G k u v) in

def IsEdgeReachable : Prop :=
  ∀ ⦃s : Set (Sym2 V)⦄, s.encard < k → (G.deleteEdges s).Reachable u v

variable (G k) in

def IsEdgeConnected : Prop := ∀ u v, G.IsEdgeReachable k u v
