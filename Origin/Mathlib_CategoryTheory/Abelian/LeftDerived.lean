/-
Extracted from CategoryTheory/Abelian/LeftDerived.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Left-derived functors

We define the left-derived functors `F.leftDerived n : C ⥤ D` for any additive functor `F`
out of a category with projective resolutions.

We first define a functor
`F.leftDerivedToHomotopyCategory : C ⥤ HomotopyCategory D (ComplexShape.down ℕ)` which is
`projectiveResolutions C ⋙ F.mapHomotopyCategory _`. We show that if `X : C` and
`P : ProjectiveResolution X`, then `F.leftDerivedToHomotopyCategory.obj X` identifies
to the image in the homotopy category of the functor `F` applied objectwise to `P.complex`
(this isomorphism is `P.isoLeftDerivedToHomotopyCategoryObj F`).

Then, the left-derived functors `F.leftDerived n : C ⥤ D` are obtained by composing
`F.leftDerivedToHomotopyCategory` with the homology functors on the homotopy category.

Similarly we define natural transformations between left-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `Functor.isZero_leftDerived_obj_projective_succ`: projective objects have no higher
  left derived functor.
* `NatTrans.leftDerived`: the natural transformation between left derived functors
  induced by a natural transformation.
* `Functor.fromLeftDerivedZero`: the natural transformation `F.leftDerived 0 ⟶ F`,
  which is an isomorphism when `F` is right exact (i.e. preserves finite colimits),
  see also `Functor.leftDerivedZeroIsoSelf`.

## TODO

* refactor `Functor.leftDerived` (and `Functor.rightDerived`) when the necessary
  material enters mathlib: derived categories, injective/projective derivability
  structures, existence of derived functors from derivability structures.
  Eventually, we shall get a left derived functor
  `F.leftDerivedFunctorMinus : DerivedCategory.Minus C ⥤ DerivedCategory.Minus D`,
  and `F.leftDerived` shall be redefined using `F.leftDerivedFunctorMinus`.

-/

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
  [Abelian C] [HasProjectiveResolutions C] [Abelian D]

noncomputable def Functor.leftDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive] :
    C ⥤ HomotopyCategory D (ComplexShape.down ℕ) :=
  projectiveResolutions C ⋙ F.mapHomotopyCategory _

noncomputable def ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.leftDerivedToHomotopyCategory.obj X ≅
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).obj P.complex :=
  (F.mapHomotopyCategory _).mapIso P.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app P.complex

set_option backward.isDefEq.respectTransparency false in
