/-
Extracted from Topology/Algebra/OpenSubgroup.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Open subgroups of a topological group

This file builds the lattice `OpenSubgroup G` of open subgroups in a topological group `G`,
and its additive version `OpenAddSubgroup`. This lattice has a top element, the subgroup of all
elements, but no bottom element in general. The trivial subgroup which is the natural candidate
bottom has no reason to be open (this happens only in discrete groups).

Note that this notion is especially relevant in a non-archimedean context, for instance for
`p`-adic groups.

## Main declarations

* `OpenSubgroup.isClosed`: An open subgroup is automatically closed.
* `Subgroup.isOpen_mono`: A subgroup containing an open subgroup is open.
                           There are also versions for additive groups, submodules and ideals.
* `OpenSubgroup.comap`: Open subgroups can be pulled back by a continuous group morphism.

## TODO
* Prove that the identity component of a locally path connected group is an open subgroup.
  Up to now this file is really geared towards non-archimedean algebra, not Lie groups.
-/

open TopologicalSpace Topology Function

structure OpenAddSubgroup (G : Type*) [AddGroup G] [TopologicalSpace G] extends AddSubgroup G where
  isOpen' : IsOpen carrier
