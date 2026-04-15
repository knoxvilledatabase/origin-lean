/-
Extracted from Geometry/RingedSpace/SheafedSpace.lean
Genuine: 3 of 9 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`).

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

open CategoryTheory TopCat TopologicalSpace Opposite CategoryTheory.Limits CategoryTheory.Category

  CategoryTheory.Functor Topology

universe u v w' w

variable (C : Type u) [Category.{v} C]

namespace AlgebraicGeometry

structure SheafedSpace extends PresheafedSpace C where
  /-- A sheafed space is a presheafed space which happens to be a sheaf. -/
  IsSheaf : presheaf.IsSheaf

variable {C}

namespace SheafedSpace

-- INSTANCE (free from Core): coeCarrier

-- INSTANCE (free from Core): coeSort

def sheaf (X : SheafedSpace C) : Sheaf C (X : TopCat) :=
  ⟨X.presheaf, X.IsSheaf⟩

-- INSTANCE (free from Core): (X

def unit (X : TopCat) : SheafedSpace (Discrete Unit) :=
  { @PresheafedSpace.const (Discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.isSheaf_unit _ }

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
