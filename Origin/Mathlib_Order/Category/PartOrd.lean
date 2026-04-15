/-
Extracted from Order/Category/PartOrd.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Category of partial orders

This defines `PartOrd`, the category of partial orders with monotone maps.
-/

open CategoryTheory

universe u

structure PartOrd where
  /-- Construct a bundled `PartOrd` from the underlying type and typeclass. -/
  of ::
  /-- The underlying partially ordered type. -/
  (carrier : Type*)
  [str : PartialOrder carrier]

attribute [instance] PartOrd.str

initialize_simps_projections PartOrd (carrier → coe, -str)

namespace PartOrd

-- INSTANCE (free from Core): :

attribute [coe] PartOrd.carrier

set_option backward.privateInPublic true in
