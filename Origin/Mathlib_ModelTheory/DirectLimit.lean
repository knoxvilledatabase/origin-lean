/-
Extracted from ModelTheory/DirectLimit.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Direct Limits of First-Order Structures

This file constructs the direct limit of a directed system of first-order embeddings.

## Main Definitions

- `FirstOrder.Language.DirectLimit G f` is the direct limit of the directed system `f` of
  first-order embeddings between the structures indexed by `G`.
- `FirstOrder.Language.DirectLimit.lift` is the universal property of the direct limit: maps
  from the components to another module that respect the directed system structure give rise to
  a unique map out of the direct limit.
- `FirstOrder.Language.DirectLimit.equiv_lift` is the equivalence between limits of
  isomorphic direct systems.
-/

universe v w w' u₁ u₂

open FirstOrder

namespace FirstOrder

namespace Language

open Structure Set

variable {L : Language} {ι : Type v} [Preorder ι]

variable {G : ι → Type w} [∀ i, L.Structure (G i)]

variable (f : ∀ i j, i ≤ j → G i ↪[L] G j)

namespace DirectedSystem

alias map_self := DirectedSystem.map_self'

alias map_map := DirectedSystem.map_map'

variable {G' : ℕ → Type w} [∀ i, L.Structure (G' i)] (f' : ∀ n : ℕ, G' n ↪[L] G' (n + 1))

def natLERec (m n : ℕ) (h : m ≤ n) : G' m ↪[L] G' n :=
  Nat.leRecOn h (@fun k g => (f' k).comp g) (Embedding.refl L _)
