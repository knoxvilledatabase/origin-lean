/-
Extracted from CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The preadditive category structure on the localized category

In this file, it is shown that if `W : MorphismProperty C` has a left calculus
of fractions, and `C` is preadditive, then the localized category is preadditive,
and the localization functor is additive.

Let `L : C ⥤ D` be a localization functor for `W`. We first construct an abelian
group structure on `L.obj X ⟶ L.obj Y` for `X` and `Y` in `C`. The addition
is defined using representatives of two morphisms in `L` as left fractions with
the same denominator thanks to the lemmas in
`CategoryTheory.Localization.CalculusOfFractions.Fractions`.
As `L` is essentially surjective, we finally transport these abelian group structures
to `X' ⟶ Y'` for all `X'` and `Y'` in `D`.

Preadditive category instances are defined on the categories `W.Localization`
(and `W.Localization'`) under the assumption that `W` has a left calculus of fractions.
(It would be easy to deduce from the results in this file that if `W` has a right calculus
of fractions, then the localized category can also be equipped with
a preadditive structure, but only one of these two constructions can be made an instance!)

-/

namespace CategoryTheory

open MorphismProperty Preadditive Limits Category

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] (L : C ⥤ D)
  {W : MorphismProperty C} [L.IsLocalization W]

namespace MorphismProperty

abbrev LeftFraction.neg {X Y : C} (φ : W.LeftFraction X Y) :
    W.LeftFraction X Y where
  Y' := φ.Y'
  f := -φ.f
  s := φ.s
  hs := φ.hs

namespace LeftFraction₂

variable {X Y : C} (φ : W.LeftFraction₂ X Y)

abbrev add : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f + φ.f'
  s := φ.s
  hs := φ.hs
