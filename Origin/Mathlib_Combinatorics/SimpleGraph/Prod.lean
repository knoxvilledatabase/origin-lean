/-
Extracted from Combinatorics/SimpleGraph/Prod.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Graph products

This file defines the box product of graphs and other product constructions. The box product of `G`
and `H` is the graph on the product of the vertices such that `x` and `y` are related iff they agree
on one component and the other one is related via either `G` or `H`. For example, the box product of
two edges is a square.

## Main declarations

* `SimpleGraph.boxProd`: The box product.

## Notation

* `G □ H`: The box product of `G` and `H`.

## TODO

Define all other graph products!
-/

variable {α β γ V V₁ V₂ W W₁ W₂ : Type*}

namespace SimpleGraph

variable {G : SimpleGraph α} {H : SimpleGraph β}

def boxProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1
  symm x y := by simp [and_comm, eq_comm, adj_comm]
  loopless := ⟨fun x ↦ by simp⟩

infixl:70 " □ " => boxProd
