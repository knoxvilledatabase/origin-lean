/-
Extracted from Order/CompleteSublattice.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Complete Sublattices

This file defines complete sublattices. These are subsets of complete lattices which are closed
under arbitrary suprema and infima. As a standard example one could take the complete sublattice of
invariant submodules of some module with respect to a linear map.

## Main definitions:
* `CompleteSublattice`: the definition of a complete sublattice
* `CompleteSublattice.mk'`: an alternate constructor for a complete sublattice, demanding fewer
  hypotheses
* `CompleteSublattice.instCompleteLattice`: a complete sublattice is a complete lattice
* `CompleteSublattice.map`: complete sublattices push forward under complete lattice morphisms.
* `CompleteSublattice.comap`: complete sublattices pull back under complete lattice morphisms.

-/

open Function Set

variable (α β : Type*) [CompleteLattice α] [CompleteLattice β] (f : CompleteLatticeHom α β)

structure CompleteSublattice extends Sublattice α where
  sSupClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sSup s ∈ carrier
  sInfClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sInf s ∈ carrier

variable {α β}

namespace CompleteSublattice
