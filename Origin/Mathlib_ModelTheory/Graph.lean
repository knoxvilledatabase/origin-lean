/-
Extracted from ModelTheory/Graph.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# First-Order Structures in Graph Theory

This file defines first-order languages, structures, and theories in graph theory.

## Main Definitions

- `FirstOrder.Language.graph` is the language consisting of a single relation representing
  adjacency.
- `SimpleGraph.structure` is the first-order structure corresponding to a given simple graph.
- `FirstOrder.Language.Theory.simpleGraph` is the theory of simple graphs.
- `FirstOrder.Language.simpleGraphOfStructure` gives the simple graph corresponding to a model
  of the theory of simple graphs.
-/

universe u

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

variable {V : Type u} {n : ℕ}

/-! ### Simple Graphs -/

inductive graphRel : ℕ → Type
  | adj : graphRel 2
  deriving DecidableEq

protected def graph : Language := ⟨fun _ => Empty, graphRel⟩
  deriving IsRelational

abbrev adj : Language.graph.Relations 2 := .adj
