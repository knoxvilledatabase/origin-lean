/-
Extracted from Algebra/Category/MonCat/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Category instances for `Monoid`, `AddMonoid`, `CommMonoid`, and `AddCommMonoid`.

We introduce the bundled categories:
* `MonCat`
* `AddMonCat`
* `CommMonCat`
* `AddCommMonCat`

along with the relevant forgetful functors between them.
-/

assert_not_exists MonoidWithZero

universe u v

open CategoryTheory

structure AddMonCat : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddMonoid carrier]
