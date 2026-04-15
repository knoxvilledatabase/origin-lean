/-
Extracted from CategoryTheory/Abelian/RightDerived.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Right-derived functors

We define the right-derived functors `F.rightDerived n : C ⥤ D` for any additive functor `F`
out of a category with injective resolutions.

We first define a functor
`F.rightDerivedToHomotopyCategory : C ⥤ HomotopyCategory D (ComplexShape.up ℕ)` which is
`injectiveResolutions C ⋙ F.mapHomotopyCategory _`. We show that if `X : C` and
`I : InjectiveResolution X`, then `F.rightDerivedToHomotopyCategory.obj X` identifies
to the image in the homotopy category of the functor `F` applied objectwise to `I.cocomplex`
(this isomorphism is `I.isoRightDerivedToHomotopyCategoryObj F`).

Then, the right-derived functors `F.rightDerived n : C ⥤ D` are obtained by composing
`F.rightDerivedToHomotopyCategory` with the homology functors on the homotopy category.

Similarly we define natural transformations between right-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `Functor.isZero_rightDerived_obj_injective_succ`: injective objects have no higher
  right derived functor.
* `NatTrans.rightDerived`: the natural transformation between right derived functors
  induced by a natural transformation.
* `Functor.toRightDerivedZero`: the natural transformation `F ⟶ F.rightDerived 0`,
  which is an isomorphism when `F` is left exact (i.e. preserves finite limits),
  see also `Functor.rightDerivedZeroIsoSelf`.

## TODO

* refactor `Functor.rightDerived` (and `Functor.leftDerived`) when the necessary
  material enters mathlib: derived categories, injective/projective derivability
  structures, existence of derived functors from derivability structures.
  Eventually, we shall get a right derived functor
  `F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`,
  and `F.rightDerived` shall be redefined using `F.rightDerivedFunctorPlus`.

-/

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D]

noncomputable def Functor.rightDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive] :
    C ⥤ HomotopyCategory D (ComplexShape.up ℕ) :=
  injectiveResolutions C ⋙ F.mapHomotopyCategory _

noncomputable def InjectiveResolution.isoRightDerivedToHomotopyCategoryObj {X : C}
    (I : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.rightDerivedToHomotopyCategory.obj X ≅
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).obj I.cocomplex :=
  (F.mapHomotopyCategory _).mapIso I.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app I.cocomplex

set_option backward.isDefEq.respectTransparency false in
