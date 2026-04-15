/-
Extracted from Order/Category/BddLat.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The category of bounded lattices

This file defines `BddLat`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/

universe u

open CategoryTheory

structure BddLat extends Lat where
  [isBoundedOrder : BoundedOrder toLat]

add_decl_doc BddLat.toLat

namespace BddLat

-- INSTANCE (free from Core): :

attribute [instance] BddLat.isBoundedOrder

abbrev of (α : Type*) [Lattice α] [BoundedOrder α] : BddLat where
  carrier := α

set_option backward.privateInPublic true in
