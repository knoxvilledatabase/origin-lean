/-
Extracted from Order/Category/BddOrd.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of bounded orders

This defines `BddOrd`, the category of bounded orders.
-/

universe u v

open CategoryTheory

structure BddOrd extends PartOrd where
  [isBoundedOrder : BoundedOrder toPartOrd]

add_decl_doc BddOrd.toPartOrd

attribute [instance] BddOrd.isBoundedOrder

initialize_simps_projections BddOrd (carrier → coe, -str)

namespace BddOrd

-- INSTANCE (free from Core): :

abbrev of (X : Type*) [PartialOrder X] [BoundedOrder X] : BddOrd where
  carrier := X

set_option backward.privateInPublic true in
