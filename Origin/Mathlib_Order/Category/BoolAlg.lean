/-
Extracted from Order/Category/BoolAlg.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of Boolean algebras

This defines `BoolAlg`, the category of Boolean algebras.
-/

open OrderDual Opposite Set

universe u

open CategoryTheory

structure BoolAlg where
  /-- Construct a bundled `BoolAlg` from the underlying type and typeclass. -/
  of ::
  /-- The underlying Boolean algebra. -/
  carrier : Type*
  [str : BooleanAlgebra carrier]

attribute [instance] BoolAlg.str

initialize_simps_projections BoolAlg (carrier → coe, -str)

namespace BoolAlg

-- INSTANCE (free from Core): :

attribute [coe] BoolAlg.carrier

set_option backward.privateInPublic true in
