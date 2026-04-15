/-
Extracted from Topology/KrullDimension.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Krull dimension of a topological space

The Krull dimension of a topological space is the order-theoretic Krull dimension applied to the
collection of all its subsets that are closed and irreducible. Unfolding this definition, it is
the length of longest series of closed irreducible subsets ordered by inclusion.

## Main results

- `topologicalKrullDim_subspace_le`: For any subspace Y ⊆ X, we have dim(Y) ≤ dim(X)

## Implementation notes

The proofs use order-preserving maps between posets of irreducible closed sets to establish
dimension inequalities.
-/

open Set Function Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

noncomputable def topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
  krullDim (IrreducibleCloseds T)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-!
### Main dimension theorems -/

theorem IsInducing.topologicalKrullDim_le {f : Y → X} (hf : IsInducing f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  krullDim_le_of_strictMono _ (map_strictMono_of_isInducing hf)
