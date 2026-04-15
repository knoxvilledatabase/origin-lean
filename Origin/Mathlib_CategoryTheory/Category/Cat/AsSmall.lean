/-
Extracted from CategoryTheory/Category/Cat/AsSmall.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.ULift

/-!
# Functorially embedding `Cat` into the category of small categories

There is a canonical functor `asSmallFunctor` between the category of categories of any size and
any larger category of small categories.

## Future Work

Show that `asSmallFunctor` is faithful.
-/

universe w v u

namespace CategoryTheory

namespace Cat

@[simps]
def asSmallFunctor : Cat.{v, u} ⥤ Cat.{max w v u, max w v u} where
  obj C := .of <| AsSmall C
  map F := AsSmall.down ⋙ F ⋙ AsSmall.up

end Cat

end CategoryTheory
