/-
Extracted from Topology/Sets/Closeds.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Closed sets

We define a few types of closed sets in a topological space.

## Main Definitions

For a topological space `α`,
* `TopologicalSpace.Closeds α`: The type of closed sets.
* `TopologicalSpace.Clopens α`: The type of clopen sets.
-/

open Order OrderDual Set Topology

variable {ι α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Closed sets -/

structure Closeds (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isClosed' : IsClosed carrier

namespace Closeds

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

theorem isClosed (s : Closeds α) : IsClosed (s : Set α) :=
  s.isClosed'

def Simps.coe (s : Closeds α) : Set α := s

initialize_simps_projections Closeds (carrier → coe, as_prefix coe)
