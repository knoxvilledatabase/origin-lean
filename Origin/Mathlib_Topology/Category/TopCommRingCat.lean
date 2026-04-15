/-
Extracted from Topology/Category/TopCommRingCat.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Category of topological commutative rings

We introduce the category `TopCommRingCat` of topological commutative rings together with the
relevant forgetful functors to topological spaces and commutative rings.
-/

universe u

open CategoryTheory

structure TopCommRingCat where
  /-- Construct a bundled `TopCommRingCat` from the underlying type and the appropriate typeclasses.
  -/
  of ::
  /-- carrier of a topological commutative ring. -/
  α : Type u
  [isCommRing : CommRing α]
  [isTopologicalSpace : TopologicalSpace α]
  [isTopologicalRing : IsTopologicalRing α]

section Notation

open Lean.PrettyPrinter.Delaborator
