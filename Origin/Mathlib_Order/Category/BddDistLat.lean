/-
Extracted from Order/Category/BddDistLat.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of bounded distributive lattices

This defines `BddDistLat`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/

universe u

open CategoryTheory

structure BddDistLat extends DistLat where
  [isBoundedOrder : BoundedOrder toDistLat]

add_decl_doc BddDistLat.toDistLat

namespace BddDistLat

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (X

attribute [instance] BddDistLat.isBoundedOrder

abbrev of (α : Type*) [DistribLattice α] [BoundedOrder α] : BddDistLat where
  carrier := α

set_option backward.privateInPublic true in
