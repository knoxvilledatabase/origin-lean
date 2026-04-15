/-
Extracted from CategoryTheory/LocallyCartesianClosed/ChosenPullbacksAlong.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chosen pullbacks along a morphism

## Main declarations

- `ChosenPullbacksAlong` : For a morphism `f : Y ⟶ X` in `C`, the type class
  `ChosenPullbacksAlong f` provides the data of a pullback functor `Over X ⥤ Over Y`
  as a right adjoint to `Over.map f`.

## Main results

- We prove that `ChosenPullbacksAlong` has good closure properties: isos have chosen pullbacks,
  and composition of morphisms with chosen pullbacks have chosen pullbacks.

- We prove that chosen pullbacks yield usual pullbacks: `ChosenPullbacksAlong.isPullback`
  proves that for morphisms `f` and `g` with the same codomain, the object
  `ChosenPullbacksAlong.pullbackObj f g` together with morphisms
  `ChosenPullbacksAlong.fst f g` and `ChosenPullbacksAlong.snd f g` form a pullback square
  over `f` and `g`.

- We prove that in cartesian monoidal categories, morphisms to the terminal tensor unit and
  the product projections have chosen pullbacks.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits CartesianMonoidalCategory MonoidalCategory Over

variable {C : Type u₁} [Category.{v₁} C]

class ChosenPullbacksAlong {Y X : C} (f : Y ⟶ X) where
  /-- The pullback functor along `f`. -/
  pullback : Over X ⥤ Over Y
  /-- The adjunction between `Over.map f` and `pullback f`. -/
  mapPullbackAdj (f) : Over.map f ⊣ pullback

variable (C) in

abbrev ChosenPullbacks := Π {X Y : C} (f : Y ⟶ X), ChosenPullbacksAlong f

namespace ChosenPullbacksAlong
