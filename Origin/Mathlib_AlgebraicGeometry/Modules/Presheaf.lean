/-
Extracted from AlgebraicGeometry/Modules/Presheaf.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of presheaves of modules over a scheme

In this file, given a scheme `X`, we define the category of presheaves
of modules over `X`. As categories of presheaves of modules are
defined for presheaves of rings (and not presheaves of commutative rings),
we also introduce a definition `X.ringCatSheaf` for the underlying sheaf
of rings of `X`.

-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X Y : Scheme.{u})

abbrev ringCatSheaf : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

nonrec abbrev PresheafOfModules := PresheafOfModules.{u} X.ringCatSheaf.obj

variable {X Y} in

def Hom.toRingCatSheafHom (f : X ⟶ Y) :
    Y.ringCatSheaf ⟶ ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      _ _ _).obj X.ringCatSheaf where
  hom := Functor.whiskerRight f.c _

end AlgebraicGeometry.Scheme
