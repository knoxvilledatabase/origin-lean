/-
Extracted from Topology/Order.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordering on topologies and (co)induced topologies

Topologies on a fixed type `α` are ordered, by reverse inclusion.  That is, for topologies `t₁` and
`t₂` on `α`, we write `t₁ ≤ t₂` if every set open in `t₂` is also open in `t₁`.  (One also calls
`t₁` *finer* than `t₂`, and `t₂` *coarser* than `t₁`.)

Any function `f : α → β` induces

* `TopologicalSpace.induced f : TopologicalSpace β → TopologicalSpace α`;
* `TopologicalSpace.coinduced f : TopologicalSpace α → TopologicalSpace β`.

Continuity, the ordering on topologies and (co)induced topologies are related as follows:

* The identity map `(α, t₁) → (α, t₂)` is continuous iff `t₁ ≤ t₂`.
* A map `f : (α, t) → (β, u)` is continuous
  * iff `t ≤ TopologicalSpace.induced f u` (`continuous_iff_le_induced`)
  * iff `TopologicalSpace.coinduced f t ≤ u` (`continuous_iff_coinduced_le`).

Topologies on `α` form a complete lattice, with `⊥` the discrete topology and `⊤` the indiscrete
topology.

For a function `f : α → β`, `(TopologicalSpace.coinduced f, TopologicalSpace.induced f)` is a Galois
connection between topologies on `α` and topologies on `β`.

## Implementation notes

There is a Galois insertion between topologies on `α` (with the inclusion ordering) and all
collections of sets in `α`. The complete lattice structure on topologies on `α` is defined as the
reverse of the one obtained via this Galois insertion. More precisely, we use the corresponding
Galois coinsertion between topologies on `α` (with the reversed inclusion ordering) and collections
of sets in `α` (with the reversed inclusion ordering).

## Tags

finer, coarser, induced topology, coinduced topology
-/

open Function Set Filter Topology

universe u v w

namespace TopologicalSpace

variable {α : Type u}

inductive GenerateOpen (g : Set (Set α)) : Set α → Prop
  | basic : ∀ s ∈ g, GenerateOpen g s
  | univ : GenerateOpen g univ
  | inter : ∀ s t, GenerateOpen g s → GenerateOpen g t → GenerateOpen g (s ∩ t)
  | sUnion : ∀ S : Set (Set α), (∀ s ∈ S, GenerateOpen g s) → GenerateOpen g (⋃₀ S)
