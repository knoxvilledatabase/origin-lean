/-
Extracted from CategoryTheory/Bicategory/Functor/Cat/ObjectProperty.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Properties of objects in target categories of a pseudofunctor to `Cat`

Given `F : Pseudofunctor B Cat`, we introduce a type `F.ObjectProperty`
which consists of properties `P` of objects for all categories `F.obj X` for `X : B`.
The typeclass `P.IsClosedUnderMapObj` expresses that this property
is preserved by the application of the functors `F.map`: this allows
to define a sub-pseudofunctor `P.fullsubcategory : Pseudofunctor B Cat`.

## TODO (@joelriou)
* Given a Grothendieck topology `J` on a category `C`, define
  a type class `Pseudofunctor.ObjectProperty.IsLocal P J` extending
  `IsClosedUnderMapObj` saying that if an object locally satisfies
  the property, then it satisfies the property. Assuming this, show that
  `P.fullsubcategory` is a stack if the original pseudofunctor was.

-/

universe w v v' u u'

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {B : Type u} [Bicategory.{w, v} B] (F : Pseudofunctor B Cat.{v', u'})

protected structure ObjectProperty where
  /-- A property of objects in the category `F.obj X` for all `X : B`. -/
  prop (X : B) : CategoryTheory.ObjectProperty (F.obj X)

namespace ObjectProperty

variable {F} (P : F.ObjectProperty)

abbrev Obj (X : B) := (P.prop X).FullSubcategory

class IsClosedUnderMapObj (P : F.ObjectProperty) : Prop where
  map_obj (P) {X Y : B} {M : F.obj X} (hM : P.prop X M) (f : X ⟶ Y) :
    P.prop Y ((F.map f).toFunctor.obj M)

export IsClosedUnderMapObj (map_obj)

class IsClosedUnderIsomorphisms : Prop where
  isClosedUnderIsomorphisms (X : B) : (P.prop X).IsClosedUnderIsomorphisms

attribute [instance] IsClosedUnderIsomorphisms.isClosedUnderIsomorphisms

variable [P.IsClosedUnderMapObj]
