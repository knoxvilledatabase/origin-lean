/-
Extracted from Topology/Category/TopCat/ULift.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lifting topological spaces to a higher universe

In this file, we construct the functor `uliftFunctor.{v, u} : TopCat.{u} ⥤ TopCat.{max u v}`
which sends a topological space `X : Type u` to a homeomorphic space in `Type (max u v)`.

-/

universe w w' v u

open CategoryTheory

namespace TopCat

def uliftFunctor : TopCat.{u} ⥤ TopCat.{max u v} where
  obj X := TopCat.of (ULift.{v} X)
  map {X Y} f := ofHom ⟨ULift.map f, by fun_prop⟩

def uliftFunctorObjHomeo (X : TopCat.{u}) : X ≃ₜ uliftFunctor.{v}.obj X :=
  Homeomorph.ulift.symm
