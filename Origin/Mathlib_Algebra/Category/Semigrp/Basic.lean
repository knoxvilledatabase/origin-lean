/-
Extracted from Algebra/Category/Semigrp/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Category instances for `Mul`, `Add`, `Semigroup` and `AddSemigroup`

We introduce the bundled categories:
* `MagmaCat`
* `AddMagmaCat`
* `Semigrp`
* `AddSemigrp`

along with the relevant forgetful functors between them.

This closely follows `Mathlib/Algebra/Category/MonCat/Basic.lean`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/

universe u v

open CategoryTheory

structure AddMagmaCat : Type (u + 1) where
  /-- The underlying additive magma. -/
  (carrier : Type u)
  [str : Add carrier]
