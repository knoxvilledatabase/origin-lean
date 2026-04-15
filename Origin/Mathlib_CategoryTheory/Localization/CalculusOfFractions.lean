/-
Extracted from CategoryTheory/Localization/CalculusOfFractions.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Calculus of fractions

Following the definitions by [Gabriel and Zisman][gabriel-zisman-1967],
given a morphism property `W : MorphismProperty C` on a category `C`,
we introduce the class `W.HasLeftCalculusOfFractions`. The main
result `Localization.exists_leftFraction` is that if `L : C ⥤ D`
is a localization functor for `W`, then for any morphism `L.obj X ⟶ L.obj Y` in `D`,
there exists an auxiliary object `Y' : C` and morphisms `g : X ⟶ Y'` and `s : Y ⟶ Y'`,
with `W s`, such that the given morphism is a sort of fraction `g / s`,
or more precisely of the form `L.map g ≫ (Localization.isoOfHom L W s hs).inv`.
We also show that the functor `L.mapArrow : Arrow C ⥤ Arrow D` is essentially surjective.

Similar results are obtained when `W` has a right calculus of fractions.

## References

* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*][gabriel-zisman-1967]

-/

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

open Category

namespace MorphismProperty

structure LeftFraction (W : MorphismProperty C) (X Y : C) where
  /-- the auxiliary object of a left fraction -/
  {Y' : C}
  /-- the numerator of a left fraction -/
  f : X ⟶ Y'
  /-- the denominator of a left fraction -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s

namespace LeftFraction

variable (W : MorphismProperty C) {X Y : C}
