/-
Extracted from Order/Category/DistLat.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of distributive lattices

This file defines `DistLat`, the category of distributive lattices.

Note that [`DistLat`](https://ncatlab.org/nlab/show/DistLat) in the literature doesn't always
correspond to `DistLat` as we don't require bottom or top elements. Instead, this `DistLat`
corresponds to `BddDistLat`.
-/

universe u

open CategoryTheory

structure DistLat where
  /-- The underlying distributive lattice. -/
  carrier : Type*
  [str : DistribLattice carrier]

attribute [instance] DistLat.str

initialize_simps_projections DistLat (carrier → coe, -str)

namespace DistLat

-- INSTANCE (free from Core): :

attribute [coe] DistLat.carrier

abbrev of (X : Type*) [DistribLattice X] : DistLat := ⟨X⟩

set_option backward.privateInPublic true in
