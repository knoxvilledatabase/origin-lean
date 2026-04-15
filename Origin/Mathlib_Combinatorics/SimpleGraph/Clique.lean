/-
Extracted from Combinatorics/SimpleGraph/Clique.lean
Genuine: 5 of 10 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Graph cliques

This file defines cliques in simple graphs.
A clique is a set of vertices that are pairwise adjacent.

## Main declarations

* `SimpleGraph.IsClique`: Predicate for a set of vertices to be a clique.
* `SimpleGraph.IsNClique`: Predicate for a set of vertices to be an `n`-clique.
* `SimpleGraph.cliqueFinset`: Finset of `n`-cliques of a graph.
* `SimpleGraph.CliqueFree`: Predicate for a graph to have no `n`-cliques.
-/

open Finset Fintype Function SimpleGraph.Walk

namespace SimpleGraph

variable {α β : Type*} (G H : SimpleGraph α)

/-! ### Cliques -/

section Clique

variable {s t : Set α}

abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj

lemma not_isClique_iff : ¬ G.IsClique s ↔ ∃ (v w : s), v ≠ w ∧ ¬ G.Adj v w := by
  aesop (add simp [isClique_iff, Set.Pairwise])

theorem isClique_iff_isChain_adj : G.IsClique s ↔ IsChain G.Adj s := by
  simp [IsChain, G.symm.iff]

-- INSTANCE (free from Core): [DecidableEq

variable {G H} {a b : α}

theorem IsClique.of_subsingleton {G : SimpleGraph α} (hs : s.Subsingleton) : G.IsClique s :=
  hs.pairwise G.Adj

lemma isClique_pair : G.IsClique {a, b} ↔ a ≠ b → G.Adj a b := Set.pairwise_pair_of_symmetric G.symm
