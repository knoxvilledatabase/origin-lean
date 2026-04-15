/-
Extracted from Combinatorics/SimpleGraph/EdgeLabeling.lean
Genuine: 5 of 13 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Edge labelings

This module defines labelings of the edges of a graph.

## Main definitions

- `SimpleGraph.EdgeLabeling`: An assignment of a label from a given type to each edge of the graph.

- `SimpleGraph.EdgeLabeling.labelGraph`: the graph consisting of all edges with a given label.
-/

open Finset

open Fintype (card)

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}

def EdgeLabeling (G : SimpleGraph V) (K : Type*) :=
  G.edgeSet → K

-- INSTANCE (free from Core): [DecidableEq

-- INSTANCE (free from Core): [Finite

-- INSTANCE (free from Core): [Nonempty

-- INSTANCE (free from Core): [Inhabited

-- INSTANCE (free from Core): [Subsingleton

-- INSTANCE (free from Core): [Nonempty

-- INSTANCE (free from Core): [Unique

abbrev TopEdgeLabeling (V K : Type*) :=
  EdgeLabeling (⊤ : SimpleGraph V) K

theorem card_topEdgeLabeling [DecidableEq V] [Fintype V] [Fintype K] :
    card (TopEdgeLabeling V K) = card K ^ (card V).choose 2 :=
  Fintype.card_fun.trans (by rw [← edgeFinset_card, card_edgeFinset_top_eq_card_choose_two])

namespace EdgeLabeling

def get (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y) : K :=
  C ⟨s(x, y), h⟩

variable {C : EdgeLabeling G K}

theorem get_comm (x y : V) (h) : C.get y x h = C.get x y h.symm := by
  simp [EdgeLabeling.get, Sym2.eq_swap]
