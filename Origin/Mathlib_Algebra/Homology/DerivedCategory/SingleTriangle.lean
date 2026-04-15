/-
Extracted from Algebra/Homology/DerivedCategory/SingleTriangle.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The distinguished triangle of a short exact sequence in an abelian category

Given a short exact short complex `S` in an abelian category, we construct
the associated distinguished triangle in the derived category:
`(singleFunctor C 0).obj S.X₁ ⟶ (singleFunctor C 0).obj S.X₂ ⟶ (singleFunctor C 0).obj S.X₃ ⟶ ...`

## TODO
* when the canonical t-structure on the derived category is formalized, refactor
  this definition to make it a particular case of the triangle induced by a short
  exact sequence in the heart of a t-structure

-/

assert_not_exists TwoSidedIdeal

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open Category DerivedCategory Pretriangulated

namespace ShortComplex

variable {S : ShortComplex C} (hS : S.ShortExact)

namespace ShortExact

noncomputable def singleδ : (singleFunctor C 0).obj S.X₃ ⟶
    ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (((SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)).hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) ≫
    (((SingleFunctors.evaluation _ _ 0).mapIso
      (singleFunctorsPostcompQIso C)).inv.app S.X₁)⟦(1 : ℤ)⟧'
