/-
Extracted from Order/Category/PartOrdEmb.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Category of partial orders, with order embeddings as morphisms

This defines `PartOrdEmb`, the category of partial orders with order embeddings
as morphisms. We also show that `PartOrdEmb` has filtered colimits.

-/

open CategoryTheory Limits

universe u

structure PartOrdEmb where
  /-- Construct a bundled `PartOrdEmb` from the underlying type and typeclass. -/
  of ::
  /-- The underlying partially ordered type. -/
  (carrier : Type*)
  [str : PartialOrder carrier]

attribute [instance] PartOrdEmb.str

initialize_simps_projections PartOrdEmb (carrier → coe, -str)

namespace PartOrdEmb

-- INSTANCE (free from Core): :

attribute [coe] PartOrdEmb.carrier

set_option backward.privateInPublic true in
