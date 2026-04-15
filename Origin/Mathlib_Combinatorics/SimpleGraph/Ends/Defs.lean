/-
Extracted from Combinatorics/SimpleGraph/Ends/Defs.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ends

This file contains a definition of the ends of a simple graph, as sections of the inverse system
assigning, to each finite set of vertices, the connected components of its complement.
-/

universe u

variable {V : Type u} (G : SimpleGraph V) (K L M : Set V)

namespace SimpleGraph

abbrev ComponentCompl :=
  (G.induce Kᶜ).ConnectedComponent

variable {G} {K L M}

abbrev componentComplMk (G : SimpleGraph V) {v : V} (vK : v ∉ K) : G.ComponentCompl K :=
  connectedComponentMk (G.induce Kᶜ) ⟨v, vK⟩

def ComponentCompl.supp (C : G.ComponentCompl K) : Set V :=
  { v : V | ∃ h : v ∉ K, G.componentComplMk h = C }
