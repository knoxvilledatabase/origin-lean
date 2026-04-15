/-
Extracted from Combinatorics/SimpleGraph/Connectivity/Connected.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
## Main definitions

* `SimpleGraph.Reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `SimpleGraph.Preconnected` and `SimpleGraph.Connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `SimpleGraph.ConnectedComponent` is the type of connected components of
  a given graph.

* `SimpleGraph.IsBridge` for whether an edge is a bridge edge

## Main statements

* `SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem` characterizes bridge edges in terms of
  there being no cycle containing them.

## TODO

`IsBridge` is unpractical: we shouldn't require the edge to be present.
See https://github.com/leanprover-community/mathlib4/issues/31690.

## Tags
trails, paths, cycles, bridge edges
-/

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}

variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

/-! ## `Reachable` and `Connected` -/

def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)

variable {G}

theorem reachable_iff_nonempty_univ {u v : V} :
    G.Reachable u v ↔ (Set.univ : Set (G.Walk u v)).Nonempty :=
  Set.nonempty_iff_univ_nonempty

lemma not_reachable_iff_isEmpty_walk {u v : V} : ¬G.Reachable u v ↔ IsEmpty (G.Walk u v) :=
  not_nonempty_iff

protected theorem Reachable.elim {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Walk u v → p) : p :=
  Nonempty.elim h hp

protected theorem Reachable.elim_path {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Path u v → p) : p := by classical exact h.elim fun q => hp q.toPath

protected theorem Walk.reachable {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : G.Reachable u v :=
  ⟨p⟩

theorem adj_le_reachable (G : SimpleGraph V) : G.Adj ≤ G.Reachable :=
  fun _ _ ↦ Adj.reachable
