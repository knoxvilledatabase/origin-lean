/-
Extracted from Topology/Algebra/Group/GroupTopology.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
### Lattice of group topologies

We define a type class `GroupTopology α` which endows a group `α` with a topology such that all
group operations are continuous.

Group topologies on a fixed group `α` are ordered, by reverse inclusion. They form a complete
lattice, with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : TopologicalSpace α → GroupTopology β`.

The additive version `AddGroupTopology α` and corresponding results are provided as well.
-/

open Set Filter TopologicalSpace Function Topology Pointwise MulOpposite

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}

structure GroupTopology (α : Type u) [Group α] : Type u
  extends TopologicalSpace α, IsTopologicalGroup α

structure AddGroupTopology (α : Type u) [AddGroup α] : Type u
  extends TopologicalSpace α, IsTopologicalAddGroup α

attribute [to_additive] GroupTopology

namespace GroupTopology

variable [Group α]
