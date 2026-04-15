/-
Extracted from Algebra/Category/FGModuleCat/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of finitely generated modules over a ring

This introduces `FGModuleCat R`, the category of finitely generated modules over a ring `R`.
It is implemented as a full subcategory on a subtype of `ModuleCat R`.

When `K` is a field,
`FGModuleCat K` is the category of finite-dimensional vector spaces over `K`.

We first create the instance as a preadditive category.
When `R` is commutative we then give the structure as an `R`-linear monoidal category.
When `R` is a field we give it the structure of a closed monoidal category
and then as a right-rigid monoidal category.

## Future work

* Show that `FGModuleCat R` is abelian when `R` is (left)-Noetherian.

-/

noncomputable section

open CategoryTheory Module

universe v w u

section Ring

variable (R : Type u) [Ring R]

def ModuleCat.isFG : ObjectProperty (ModuleCat.{v} R) :=
  fun V ↦ Module.Finite R V

variable {R} in

abbrev FGModuleCat := (ModuleCat.isFG.{v} R).FullSubcategory

variable {R}
