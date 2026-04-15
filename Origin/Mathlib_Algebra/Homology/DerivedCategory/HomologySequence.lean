/-
Extracted from Algebra/Homology/DerivedCategory/HomologySequence.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The homology sequence

In this file, we construct `homologyFunctor C n : DerivedCategory C ⥤ C` for all `n : ℤ`,
show that they are homological functors which form a shift sequence, and construct
the long exact homology sequences associated to distinguished triangles in the
derived category.

-/

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace DerivedCategory

noncomputable def homologyFunctor (n : ℤ) : DerivedCategory C ⥤ C :=
  HomologicalComplexUpToQuasiIso.homologyFunctor C (ComplexShape.up ℤ) n

noncomputable def homologyFunctorFactors (n : ℤ) : Q ⋙ homologyFunctor C n ≅
    HomologicalComplex.homologyFunctor _ _ n :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactors C (ComplexShape.up ℤ) n

set_option backward.isDefEq.respectTransparency false in

variable {C} in
