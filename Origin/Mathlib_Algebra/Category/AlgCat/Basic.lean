/-
Extracted from Algebra/Category/AlgCat/Basic.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `AlgCat` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

open CategoryTheory Limits

universe v u

variable (R : Type u) [CommRing R]

set_option backward.privateInPublic true in

structure AlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [isRing : Ring carrier]
  [isAlgebra : Algebra R carrier]

attribute [instance] AlgCat.isRing AlgCat.isAlgebra

initialize_simps_projections AlgCat (-isRing, -isAlgebra)

namespace AlgCat

-- INSTANCE (free from Core): :

attribute [coe] AlgCat.carrier

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

abbrev of (X : Type v) [Ring X] [Algebra R X] : AlgCat.{v} R :=
  ⟨X⟩

variable {R} in

set_option backward.privateInPublic true in
