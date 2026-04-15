/-
Extracted from Topology/Category/TopCat/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Category instance for topological spaces

We introduce the bundled category `TopCat` of topological spaces together with the functors
`TopCat.discrete` and `TopCat.trivial` from the category of types to `TopCat` which equip a type
with the corresponding discrete, resp. trivial, topology. For a proof that these functors are left,
resp. right adjoint to the forgetful functor, see
`Mathlib/Topology/Category/TopCat/Adjunctions.lean`.
-/

assert_not_exists Module

open CategoryTheory TopologicalSpace Topology

universe u

structure TopCat where
  /-- The object in `TopCat` associated to a type equipped with the appropriate
  typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [str : TopologicalSpace carrier]

section Notation

open Lean.PrettyPrinter.Delaborator
