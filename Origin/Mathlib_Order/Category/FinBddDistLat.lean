/-
Extracted from Order/Category/FinBddDistLat.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of finite bounded distributive lattices

This file defines `FinBddDistLat`, the category of finite distributive lattices with
bounded lattice homomorphisms.
-/

universe u

open CategoryTheory

structure FinBddDistLat extends BddDistLat where
  [isFintype : Fintype carrier]

namespace FinBddDistLat

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (X

-- INSTANCE (free from Core): (X

attribute [instance] FinBddDistLat.isFintype

abbrev of (α : Type*) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDistLat where
  carrier := α

abbrev of' (α : Type*) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLat where
  carrier := α
  isBoundedOrder := Fintype.toBoundedOrder α

set_option backward.privateInPublic true in
