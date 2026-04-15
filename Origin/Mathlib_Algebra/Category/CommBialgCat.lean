/-
Extracted from Algebra/Category/CommBialgCat.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The category of commutative bialgebras over a commutative ring

This file defines the bundled category `CommBialgCat R` of commutative bialgebras over a fixed
commutative ring `R` along with the forgetful functor to `CommAlgCat`.
-/

noncomputable section

open Bialgebra Coalgebra Opposite CategoryTheory Limits MonObj

open scoped MonoidalCategory

universe v u

variable {R : Type u} [CommRing R]

variable (R) in

set_option backward.privateInPublic true in

structure CommBialgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [bialgebra : Bialgebra R carrier]

namespace CommBialgCat

variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

attribute [instance] commRing bialgebra

initialize_simps_projections CommBialgCat (-commRing, -bialgebra)

-- INSTANCE (free from Core): :

attribute [coe] CommBialgCat.carrier

variable (R) in

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

abbrev of (X : Type v) [CommRing X] [Bialgebra R X] : CommBialgCat.{v} R := ⟨X⟩

variable (R) in

set_option backward.privateInPublic true in
