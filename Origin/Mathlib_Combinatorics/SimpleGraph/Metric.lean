/-
Extracted from Combinatorics/SimpleGraph/Metric.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Graph metric

This module defines the `SimpleGraph.edist` function, which takes pairs of vertices to the length of
the shortest walk between them, or `⊤` if they are disconnected. It also defines `SimpleGraph.dist`
which is the `ℕ`-valued version of `SimpleGraph.edist`.

## Main definitions

- `SimpleGraph.edist` is the graph extended metric.
- `SimpleGraph.dist` is the graph metric.

## TODO

- Provide an additional computable version of `SimpleGraph.dist`
  for when `G` is connected.

- When directed graphs exist, a directed notion of distance,
  likely `ENat`-valued.

## Tags

graph metric, distance

-/

assert_not_exists Field

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ## Metric -/

section edist

noncomputable def edist (u v : V) : ℕ∞ :=
  ⨅ w : G.Walk u v, w.length

variable {G} {u v w : V}

protected theorem Reachable.exists_walk_length_eq_edist (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  csInf_mem <| Set.range_nonempty_iff_nonempty.mpr hr

protected theorem Connected.exists_walk_length_eq_edist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  (hconn u v).exists_walk_length_eq_edist

theorem edist_le (p : G.Walk u v) :
    G.edist u v ≤ p.length :=
  sInf_le ⟨p, rfl⟩

protected alias Walk.edist_le := edist_le
