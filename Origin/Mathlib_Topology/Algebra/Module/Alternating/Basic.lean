/-
Extracted from Topology/Algebra/Module/Alternating/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous alternating multilinear maps

In this file we define bundled continuous alternating maps and develop basic API about these
maps, by reusing API about continuous multilinear maps and alternating maps.

## Notation

`M [⋀^ι]→L[R] N`: notation for `R`-linear continuous alternating maps from `M` to `N`; the arguments
are indexed by `i : ι`.

## Keywords

multilinear map, alternating map, continuous
-/

open Function Matrix

structure ContinuousAlternatingMap (R M N ι : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [AddCommMonoid N] [Module R N] [TopologicalSpace N] extends
    ContinuousMultilinearMap R (fun _ : ι => M) N, M [⋀^ι]→ₗ[R] N where

add_decl_doc ContinuousAlternatingMap.toContinuousMultilinearMap

add_decl_doc ContinuousAlternatingMap.toAlternatingMap
