/-
Extracted from Algebra/Category/CoalgCat/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of coalgebras over a commutative ring

We introduce the bundled category `CoalgCat` of coalgebras over a fixed commutative ring `R`
along with the forgetful functor to `ModuleCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

structure CoalgCat extends ModuleCat.{v} R where
  instCoalgebra : Coalgebra R carrier

attribute [instance] CoalgCat.instCoalgebra

variable {R}

namespace CoalgCat

open Coalgebra

-- INSTANCE (free from Core): :
