/-
Extracted from Topology/UniformSpace/Closeds.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Hausdorff uniformity

This file defines the Hausdorff uniformity on the types of closed subsets, compact subsets and
and nonempty compact subsets of a uniform space. This is the generalization of the uniformity
induced by the Hausdorff metric to hyperspaces of uniform spaces.
-/

open Topology

open scoped Uniformity Filter

variable {α β γ : Type*}

section hausdorffEntourage

open SetRel

def hausdorffEntourage (U : SetRel α α) : SetRel (Set α) (Set α) :=
  {x | x.1 ⊆ U.preimage x.2 ∧ x.2 ⊆ U.image x.1}
