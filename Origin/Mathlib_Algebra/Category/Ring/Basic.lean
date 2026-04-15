/-
Extracted from Algebra/Category/Ring/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Category instances for `Semiring`, `Ring`, `CommSemiring`, and `CommRing`.

We introduce the bundled categories:
* `SemiRingCat`
* `RingCat`
* `CommSemiRingCat`
* `CommRingCat`

along with the relevant forgetful functors between them.
-/

universe u v

open CategoryTheory

structure SemiRingCat where
  /-- The object in the category of semirings associated to a type equipped with the appropriate
  typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [semiring : Semiring carrier]

section Notation

open Lean.PrettyPrinter.Delaborator
