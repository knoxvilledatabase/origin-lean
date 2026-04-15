/-
Extracted from Topology/Order/Lattice.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Topological lattices

In this file we define mixin classes `ContinuousInf` and `ContinuousSup`. We define the
class `TopologicalLattice` as a topological space and lattice `L` extending `ContinuousInf` and
`ContinuousSup`.

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

topological, lattice
-/

open Filter

open Topology

class ContinuousInf (L : Type*) [TopologicalSpace L] [Min L] : Prop where
  /-- The infimum is continuous -/
  continuous_inf : Continuous fun p : L × L => p.1 ⊓ p.2

class ContinuousSup (L : Type*) [TopologicalSpace L] [Max L] : Prop where
  /-- The supremum is continuous -/
  continuous_sup : Continuous fun p : L × L => p.1 ⊔ p.2

-- INSTANCE (free from Core): OrderDual.continuousSup

-- INSTANCE (free from Core): OrderDual.continuousInf

class TopologicalLattice (L : Type*) [TopologicalSpace L] [Lattice L] : Prop
  extends ContinuousInf L, ContinuousSup L

-- INSTANCE (free from Core): OrderDual.topologicalLattice

-- INSTANCE (free from Core): (priority

variable {L X : Type*} [TopologicalSpace L] [TopologicalSpace X]
