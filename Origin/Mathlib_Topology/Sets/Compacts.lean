/-
Extracted from Topology/Sets/Compacts.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Compact sets

We define a few types of compact sets in a topological space.

## Main Definitions

For a topological space `α`,
* `TopologicalSpace.Compacts α`: The type of compact sets.
* `TopologicalSpace.NonemptyCompacts α`: The type of non-empty compact sets.
* `TopologicalSpace.PositiveCompacts α`: The type of compact sets with non-empty interior.
* `TopologicalSpace.CompactOpens α`: The type of compact open sets. This is a central object in the
  study of spectral spaces.
-/

open Set

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

/-! ### Compact sets -/

structure Compacts (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isCompact' : IsCompact carrier

namespace Compacts

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def Simps.coe (s : Compacts α) : Set α := s

initialize_simps_projections Compacts (carrier → coe, as_prefix coe)

protected theorem isCompact (s : Compacts α) : IsCompact (s : Set α) :=
  s.isCompact'

-- INSTANCE (free from Core): (K
