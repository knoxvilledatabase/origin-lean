/-
Extracted from Combinatorics/SimpleGraph/Girth.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Girth of a simple graph

This file defines the girth and the extended girth of a simple graph as the length of its smallest
cycle, they give `0` or `∞` respectively if the graph is acyclic.

## TODO

- Prove that `G.egirth ≤ 2 * G.ediam + 1` and `G.girth ≤ 2 * G.diam + 1` when the diameter is
  non-zero.

-/

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α}

section egirth

noncomputable def egirth (G : SimpleGraph α) : ℕ∞ :=
  ⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length
