/-
Extracted from Algebra/Homology/DerivedCategory/ExactFunctor.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# An exact functor induces a functor on derived categories

In this file, we show that if `F : C₁ ⥤ C₂` is an exact functor between
abelian categories, then there is an induced triangulated functor
`F.mapDerivedCategory : DerivedCategory C₁ ⥤ DerivedCategory C₂`.

-/

assert_not_exists TwoSidedIdeal

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory Category Limits

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

namespace CategoryTheory.Functor

noncomputable def mapDerivedCategory : DerivedCategory C₁ ⥤ DerivedCategory C₂ :=
  F.mapHomologicalComplexUpToQuasiIso (ComplexShape.up ℤ)

noncomputable def mapDerivedCategoryFactors :
    DerivedCategory.Q ⋙ F.mapDerivedCategory ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  F.mapHomologicalComplexUpToQuasiIsoFactors _
