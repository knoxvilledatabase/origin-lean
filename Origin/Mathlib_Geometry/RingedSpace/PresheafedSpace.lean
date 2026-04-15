/-
Extracted from Geometry/RingedSpace/PresheafedSpace.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`).

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

open Opposite CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace

  Topology

variable (C : Type*) [Category* C]

namespace AlgebraicGeometry

structure PresheafedSpace.{u} where
  carrier : TopCat.{u}
  protected presheaf : carrier.Presheaf C

variable {C}

namespace PresheafedSpace

-- INSTANCE (free from Core): coeCarrier

attribute [coe] PresheafedSpace.carrier

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (X

def const (X : TopCat) (Z : C) : PresheafedSpace C where
  carrier := X
  presheaf := (Functor.const _).obj Z

-- INSTANCE (free from Core): [Inhabited

structure Hom (X Y : PresheafedSpace C) where
  base : (X : TopCat) ⟶ (Y : TopCat)
  c : Y.presheaf ⟶ base _* X.presheaf
