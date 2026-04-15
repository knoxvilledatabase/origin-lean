/-
Extracted from Topology/Compactness/SigmaCompact.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sigma-compactness in topological spaces

## Main definitions
* `IsSigmaCompact`: a set that is the union of countably many compact sets.
* `SigmaCompactSpace X`: `X` is a σ-compact topological space; i.e., is the union
  of a countable collection of compact subspaces.

-/

open Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

def IsSigmaCompact (s : Set X) : Prop :=
  ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = s

lemma IsCompact.isSigmaCompact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s :=
  ⟨fun _ => s, fun _ => hs, iUnion_const _⟩
