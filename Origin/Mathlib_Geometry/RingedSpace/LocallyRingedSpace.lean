/-
Extracted from Geometry/RingedSpace/LocallyRingedSpace.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The category of locally ringed spaces

We define (bundled) locally ringed spaces (as `SheafedSpace CommRing` along with the fact that the
stalks are local rings), and morphisms between these (morphisms in `SheafedSpace` with
`IsLocalHom` on the stalk maps).
-/

universe u

open CategoryTheory

open TopCat

open TopologicalSpace Topology

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

namespace AlgebraicGeometry

structure LocallyRingedSpace extends SheafedSpace CommRingCat.{u} where
  /-- Stalks of a locally ringed space are local rings. -/
  isLocalRing : ∀ x, IsLocalRing (presheaf.stalk x)

attribute [instance] LocallyRingedSpace.isLocalRing

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

abbrev toRingedSpace : RingedSpace :=
  X.toSheafedSpace

def toTopCat : TopCat :=
  X.1.carrier

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (x

def 𝒪 : Sheaf CommRingCat X.toTopCat :=
  X.sheaf
