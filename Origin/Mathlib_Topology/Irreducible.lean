/-
Extracted from Topology/Irreducible.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Irreducibility in topological spaces

## Main definitions

* `IrreducibleSpace`: a typeclass applying to topological spaces, stating that the space
  is nonempty and does not admit a nontrivial pair of disjoint opens.
* `IsIrreducible`: for a nonempty set in a topological space, the property that the set is an
  irreducible space in the subspace topology.

## On the definition of irreducible and connected sets/spaces

In informal mathematics, irreducible spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `IsPreirreducible`.
In other words, the only difference is whether the empty space counts as irreducible.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.

-/

open Set Topology

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Preirreducible

def IsPreirreducible (s : Set X) : Prop :=
  ∀ u v : Set X, IsOpen u → IsOpen v → (s ∩ u).Nonempty → (s ∩ v).Nonempty → (s ∩ (u ∩ v)).Nonempty
