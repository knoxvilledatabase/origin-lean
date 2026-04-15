/-
Extracted from Algebra/Category/HopfAlgCat/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of Hopf algebras over a commutative ring

We introduce the bundled category `HopfAlgCat` of Hopf algebras over a fixed commutative ring
`R` along with the forgetful functor to `BialgCat`.

This file mimics `Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat.lean`.

-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

set_option backward.privateInPublic true in

structure HopfAlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [instRing : Ring carrier]
  [instHopfAlgebra : HopfAlgebra R carrier]

attribute [instance] HopfAlgCat.instHopfAlgebra HopfAlgCat.instRing

variable {R}

namespace HopfAlgCat

open HopfAlgebra

-- INSTANCE (free from Core): :

variable (R) in

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

abbrev of (X : Type v) [Ring X] [HopfAlgebra R X] :
    HopfAlgCat R where
  carrier := X
