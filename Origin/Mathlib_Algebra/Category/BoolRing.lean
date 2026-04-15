/-
Extracted from Algebra/Category/BoolRing.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of Boolean rings

This file defines `BoolRing`, the category of Boolean rings.

## TODO

Finish the equivalence with `BoolAlg`.
-/

universe u

open CategoryTheory Order

structure BoolRing where
  /-- Construct a bundled `BoolRing` from a `BooleanRing`. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [booleanRing : BooleanRing carrier]

namespace BoolRing

initialize_simps_projections BoolRing (-booleanRing)

-- INSTANCE (free from Core): :

attribute [coe] carrier

attribute [instance] booleanRing

-- INSTANCE (free from Core): :

variable {R} in

set_option backward.privateInPublic true in
