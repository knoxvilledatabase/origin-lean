/-
Extracted from Order/Category/HeytAlg.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of Heyting algebras

This file defines `HeytAlg`, the category of Heyting algebras.
-/

universe u

open CategoryTheory Opposite Order

structure HeytAlg where
  /-- The underlying Heyting algebra. -/
  carrier : Type*
  [str : HeytingAlgebra carrier]

attribute [instance] HeytAlg.str

initialize_simps_projections HeytAlg (carrier → coe, -str)

namespace HeytAlg

-- INSTANCE (free from Core): :

attribute [coe] HeytAlg.carrier

abbrev of (X : Type*) [HeytingAlgebra X] : HeytAlg := ⟨X⟩

set_option backward.privateInPublic true in
