/-
Extracted from Topology/Homotopy/TopCat/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homotopies between morphisms in `TopCat`

In this file, we define the type `TopCat.Homotopy` of homotopies
between two morphisms in the category `TopCat`.

-/

universe u

open CategoryTheory MonoidalCategory

namespace TopCat

variable {X Y : TopCat.{u}}

abbrev Homotopy (f g : X ⟶ Y) := ContinuousMap.Homotopy f.hom g.hom

namespace Homotopy

variable {f g : X ⟶ Y} (H : Homotopy f g)

def h (H : Homotopy f g) : X ⊗ I ⟶ Y :=
  (β_ _ _).hom ≫ ofHom (H.toContinuousMap.comp (ContinuousMap.prodMap I.homeomorph (.id _)))
