/-
Extracted from CategoryTheory/Center/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The center of a category

Given a category `C`, we introduce an abbreviation `CatCenter C` for
the center of the category `C`, which is `End (𝟭 C)`, the
type of endomorphisms of the identity functor of `C`.

## References
* https://ncatlab.org/nlab/show/center+of+a+category

-/

universe v u

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

abbrev CatCenter := End (𝟭 C)

namespace CatCenter

variable {C}

abbrev app (x : CatCenter C) (X : C) : X ⟶ X := NatTrans.app x X
