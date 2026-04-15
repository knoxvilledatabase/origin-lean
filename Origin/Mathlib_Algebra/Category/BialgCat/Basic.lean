/-
Extracted from Algebra/Category/BialgCat/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of bialgebras over a commutative ring

We introduce the bundled category `BialgCat` of bialgebras over a fixed commutative ring `R`
along with the forgetful functors to `CoalgCat` and `AlgCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

structure BialgCat where
  /-- The underlying type. -/
  carrier : Type v
  [instRing : Ring carrier]
  [instBialgebra : Bialgebra R carrier]

attribute [instance] BialgCat.instBialgebra BialgCat.instRing

variable {R}

namespace BialgCat

open Bialgebra

-- INSTANCE (free from Core): :

variable (R) in
