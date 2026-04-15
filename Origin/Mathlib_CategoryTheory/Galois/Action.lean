/-
Extracted from CategoryTheory/Galois/Action.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Induced functor to finite `Aut F`-sets

Any (fiber) functor `F : C ⥤ FintypeCat` factors via the forgetful functor
from finite `Aut F`-sets to finite sets. In this file we collect basic properties
of the induced functor `H : C ⥤ Action FintypeCat (Aut F)`.

See `Mathlib/CategoryTheory/Galois/Full.lean` for the proof that `H` is (faithfully) full.

-/

universe u

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable {C : Type*} [Category* C] (F : C ⥤ FintypeCat.{u})

def functorToAction : C ⥤ Action FintypeCat.{u} (Aut F) where
  obj X := Action.FintypeCat.ofMulAction (Aut F) (F.obj X)
  map f := {
    hom := F.map f
    comm := fun g ↦ symm <| g.hom.naturality f
  }
