/-
Extracted from Combinatorics/SimpleGraph/LineGraph.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# LineGraph

## Main definitions

* `SimpleGraph.lineGraph` is the line graph of a simple graph `G`, with vertices as the edges of `G`
  and two vertices of the line graph adjacent if the corresponding edges share a vertex in `G`.

## Tags

line graph
-/

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}

variable (G) in

def lineGraph : SimpleGraph G.edgeSet where
  Adj e₁ e₂ := e₁ ≠ e₂ ∧ (e₁ ∩ e₂ : Set V).Nonempty
  symm e₁ e₂ := by intro h; rwa [ne_comm, Set.inter_comm]

lemma lineGraph_adj_iff_exists {e₁ e₂ : G.edgeSet} :
    (G.lineGraph).Adj e₁ e₂ ↔ e₁ ≠ e₂ ∧ ∃ v, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V) := by
  simp [Set.Nonempty, lineGraph]
