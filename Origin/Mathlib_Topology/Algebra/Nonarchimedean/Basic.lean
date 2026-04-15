/-
Extracted from Topology/Algebra/Nonarchimedean/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Nonarchimedean Topology

In this file we set up the theory of nonarchimedean topological groups and rings.

A nonarchimedean group is a topological group whose topology admits a basis of
open neighborhoods of the identity element in the group consisting of open subgroups.
A nonarchimedean ring is a topological ring whose underlying topological (additive)
group is nonarchimedean.

## Definitions

- `NonarchimedeanAddGroup`: nonarchimedean additive group.
- `NonarchimedeanGroup`: nonarchimedean multiplicative group.
- `NonarchimedeanRing`: nonarchimedean ring.

-/

open Topology

open scoped Pointwise

class NonarchimedeanAddGroup (G : Type*) [AddGroup G] [TopologicalSpace G] : Prop
  extends IsTopologicalAddGroup G where
  is_nonarchimedean : ∀ U ∈ 𝓝 (0 : G), ∃ V : OpenAddSubgroup G, (V : Set G) ⊆ U
