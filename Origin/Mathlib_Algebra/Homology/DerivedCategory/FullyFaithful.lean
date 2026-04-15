/-
Extracted from Algebra/Homology/DerivedCategory/FullyFaithful.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-! # The fully faithful embedding of the abelian category in its derived category

In this file, we show that for any `n : ℤ`, the functor
`singleFunctor C n : C ⥤ DerivedCategory C` is fully faithful.

-/

universe w v u

open CategoryTheory

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

noncomputable def singleFunctorCompHomologyFunctorIso (n : ℤ) :
    singleFunctor C n ⋙ homologyFunctor C n ≅ 𝟭 C :=
  Functor.isoWhiskerRight ((SingleFunctors.evaluation _ _ n).mapIso
    (singleFunctorsPostcompQIso C)) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (homologyFunctorFactors C n) ≪≫
      (HomologicalComplex.homologyFunctorSingleIso _ _ _)

-- INSTANCE (free from Core): (n

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (n

end DerivedCategory
