/-
Extracted from CategoryTheory/LocallyCartesianClosed/Over.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cartesian monoidal structure on slices induced by chosen pullbacks

## Main declarations

- `cartesianMonoidalCategoryOver` provides a cartesian monoidal structure on the slice categories
  `Over X` for all objects `X : C`, induced by chosen pullbacks in the base category `C`.
  This is the computable analogue of the noncomputable instance
  `CategoryTheory.Over.cartesianMonoidalCategory`.

- For a cartesian monoidal category `C`, and for any object `X` of `C`,
  `toOver X` is a functor from `C` to `Over X` which maps an object `A : C` to the projection
  `A ⊗ X ⟶ X` in `Over X`. This is the computable analogue of the functor `Over.star`.

## Main results

- `cartesianMonoidalCategoryOver` proves that the slices of a category with chosen pullbacks are
  cartesian monoidal.

- `toOverPullbackIsoToOver` shows that in a category with chosen pullbacks, for any morphism
  `f : Y ⟶ X`, the functors `toOver X ⋙ pullback f` and `toOver Y` are naturally isomorphic.

- `toOverIteratedSliceForwardIsoPullback` shows that in a category with chosen pullbacks the functor
  `pullback f : Over X ⥤ Over Y` is naturally isomorphic to
  `toOver (Over.mk f) : Over X ⥤ Over (Over.mk f)` post-composed with the iterated slice equivalence
  `Over (Over.mk f) ⥤ Over Y`. Note that the functor `toOver (Over.mk f)` exists by the result
  `cartesianMonoidalCategoryOver`.

### TODO

- Show that the functors `pullback f` are monoidal with respect to
  the cartesian monoidal structures on slices.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category

namespace ChosenPullbacksAlong

open CartesianMonoidalCategory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]

open Limits

variable {X : C} (Y Z : Over X)

set_option backward.isDefEq.respectTransparency false in

abbrev binaryFan [ChosenPullbacksAlong Z.hom] : BinaryFan Y Z :=
  BinaryFan.mk (P := (pullback Z.hom ⋙ Over.map Z.hom).obj (Over.mk Y.hom))
    (fst' Y.hom Z.hom) (snd' Y.hom Z.hom)

set_option backward.isDefEq.respectTransparency false in

def binaryFanIsBinaryProduct [ChosenPullbacksAlong Z.hom] :
    IsLimit (binaryFan Y Z) :=
  BinaryFan.IsLimit.mk (binaryFan Y Z)
    (fun u v => Over.homMk (lift (u.left) (v.left) (by rw [Over.w u, Over.w v])) (by simp))
    (by cat_disch) (by cat_disch)
    (fun a b m h₁ h₂ => by
      ext
      dsimp [Over.map, Comma.mapRight]
      cat_disch)

end
