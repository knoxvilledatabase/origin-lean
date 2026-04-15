/-
Extracted from Combinatorics/SimpleGraph/Hamiltonian.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Hamiltonian Graphs

In this file we introduce Hamiltonian paths, cycles and graphs.

## Main definitions

- `SimpleGraph.Walk.IsHamiltonian`: Predicate for a walk to be Hamiltonian.
- `SimpleGraph.Walk.IsHamiltonianCycle`: Predicate for a walk to be a Hamiltonian cycle.
- `SimpleGraph.IsHamiltonian`: Predicate for a graph to be Hamiltonian.
-/

open Finset Function

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}

variable {β : Type*} [DecidableEq β] {H : SimpleGraph β}

variable {a b v : α} {p : G.Walk a b} {f : G →g H}

namespace Walk

def IsHamiltonian (p : G.Walk a b) : Prop := ∀ a, p.support.count a = 1

variable (f) in

lemma IsHamiltonian.map (hf : Bijective f) (hp : p.IsHamiltonian) :
    (p.map f).IsHamiltonian := by
  simp [IsHamiltonian, hf.surjective.forall, hf.injective, hp _]
