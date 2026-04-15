/-
Extracted from Algebra/Category/Grp/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Category instances for Group, AddGroup, CommGroup, and AddCommGroup.

We introduce the bundled categories:
* `GrpCat`
* `AddGrpCat`
* `CommGrpCat`
* `AddCommGrpCat`

along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

universe u v

open CategoryTheory

structure AddGrpCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddGroup carrier]
