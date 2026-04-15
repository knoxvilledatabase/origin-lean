/-
Extracted from Order/Category/Lat.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of lattices

This defines `Lat`, the category of lattices.

Note that `Lat` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BddLat`.

## TODO

The free functor from `Lat` to `BddLat` is `X → WithTop (WithBot X)`.
-/

universe u

open CategoryTheory

structure Lat where
  /-- The underlying lattices. -/
  (carrier : Type*)
  [str : Lattice carrier]

attribute [instance] Lat.str

initialize_simps_projections Lat (carrier → coe, -str)

namespace Lat

-- INSTANCE (free from Core): :

attribute [coe] Lat.carrier

abbrev of (X : Type*) [Lattice X] : Lat := ⟨X⟩

set_option backward.privateInPublic true in
