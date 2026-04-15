/-
Extracted from Algebra/Category/CommAlgCat/Basic.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The category of commutative algebras over a commutative ring

This file defines the bundled category `CommAlgCat` of commutative algebras over a fixed commutative
ring `R` along with the forgetful functors to `CommRingCat` and `AlgCat`.
-/

open CategoryTheory Limits

universe w v u

variable {R : Type u} [CommRing R]

variable (R) in

set_option backward.privateInPublic true in

structure CommAlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]

namespace CommAlgCat

variable {A B C : CommAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

attribute [instance] commRing algebra

initialize_simps_projections CommAlgCat (-commRing, -algebra)

-- INSTANCE (free from Core): :

attribute [coe] carrier

variable (R) in

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

abbrev of (X : Type v) [CommRing X] [Algebra R X] : CommAlgCat.{v} R := ⟨X⟩

variable (R) in

set_option backward.privateInPublic true in
