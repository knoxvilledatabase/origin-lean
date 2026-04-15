/-
Extracted from Order/Category/CompleteLat.lean
Genuine: 1 of 7 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# The category of complete lattices

This file defines `CompleteLat`, the category of complete lattices.
-/

universe u

open CategoryTheory

structure CompleteLat where
  /-- Construct a bundled `CompleteLat` from the underlying type and typeclass. -/
  of ::
  /-- The underlying lattice. -/
  (carrier : Type*)
  [str : CompleteLattice carrier]

attribute [instance] CompleteLat.str

initialize_simps_projections CompleteLat (carrier → coe, -str)

namespace CompleteLat

-- INSTANCE (free from Core): :

attribute [coe] CompleteLat.carrier

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): hasForgetToBddLat
