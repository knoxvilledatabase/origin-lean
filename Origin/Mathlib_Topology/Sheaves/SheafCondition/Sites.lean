/-
Extracted from Topology/Sheaves/SheafCondition/Sites.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Coverings and sieves; from sheaves on sites and sheaves on spaces

In this file, we connect coverings in a topological space to sieves in the associated Grothendieck
topology, in preparation of connecting the sheaf condition on sites to the various sheaf conditions
on spaces.

We also specialize results about sheaves on sites to sheaves on spaces; we show that the inclusion
functor from a topological basis to `TopologicalSpace.Opens` is cover dense, that open maps
induce cover-preserving functors, and that open embeddings induce continuous functors.

-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe w v u

namespace TopCat.Presheaf

variable {X : TopCat.{w}}

def coveringOfPresieve (U : Opens X) (R : Presieve U) : (Σ V, { f : V ⟶ U // R f }) → Opens X :=
  fun f => f.1
