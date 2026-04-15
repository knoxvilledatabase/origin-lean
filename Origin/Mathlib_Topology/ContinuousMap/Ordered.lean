/-
Extracted from Topology/ContinuousMap/Ordered.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Bundled continuous maps into orders, with order-compatible topology

-/

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

namespace ContinuousMap

/-!
We now set up the partial order and lattice structure (given by pointwise min and max)
on continuous functions.
-/

-- INSTANCE (free from Core): partialOrder

theorem le_def [PartialOrder β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
  Pi.le_def

theorem lt_def [PartialOrder β] {f g : C(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a :=
  Pi.lt_def

section SemilatticeSup

variable [SemilatticeSup β] [ContinuousSup β]

-- INSTANCE (free from Core): sup
