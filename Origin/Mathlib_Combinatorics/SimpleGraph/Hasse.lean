/-
Extracted from Combinatorics/SimpleGraph/Hasse.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Hasse diagram as a graph

This file defines the Hasse diagram of an order (graph of `CovBy`, the covering relation) and the
path graph on `n` vertices.

## Main declarations

* `SimpleGraph.hasse`: Hasse diagram of an order.
* `SimpleGraph.pathGraph`: Path graph on `n` vertices.
-/

open Order OrderDual Relation

namespace SimpleGraph

variable (α β : Type*)

section Preorder

variable [Preorder α]

def hasse : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a
  symm _a _b := Or.symm
  loopless := ⟨fun _a h ↦ h.elim (irrefl _) (irrefl _)⟩

variable {α β} {a b : α}
