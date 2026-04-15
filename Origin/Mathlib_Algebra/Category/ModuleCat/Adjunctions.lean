/-
Extracted from Algebra/Category/ModuleCat/Adjunctions.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
The functor of forming finitely supported functions on a type with values in a `[Ring R]`
is the left adjoint of
the forgetful functor from `R`-modules to types.
-/

assert_not_exists Cardinal

noncomputable section

open CategoryTheory

namespace ModuleCat

universe u

variable (R : Type u)

variable [Ring R]

def free : Type u ⥤ ModuleCat R where
  obj X := ModuleCat.of R (X →₀ R)
  map {_ _} f := ofHom <| Finsupp.lmapDomain _ _ (f : _ → _)

variable {R}

noncomputable def freeMk {X : Type u} (x : X) : (free R).obj X := Finsupp.single x 1
