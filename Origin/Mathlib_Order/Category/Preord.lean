/-
Extracted from Order/Category/Preord.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Category of preorders

This defines `Preord`, the category of preorders with monotone maps.
-/

universe u

open CategoryTheory

structure Preord where
  /-- Construct a bundled `Preord` from the underlying type and typeclass. -/
  of ::
  /-- The underlying preordered type. -/
  (carrier : Type*)
  [str : Preorder carrier]

attribute [instance] Preord.str

initialize_simps_projections Preord (carrier → coe, -str)

namespace Preord

-- INSTANCE (free from Core): :

attribute [coe] Preord.carrier

set_option backward.privateInPublic true in
