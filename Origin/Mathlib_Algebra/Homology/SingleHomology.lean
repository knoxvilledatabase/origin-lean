/-
Extracted from Algebra/Homology/SingleHomology.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The homology of single complexes

The main definition in this file is `HomologicalComplex.homologyFunctorSingleIso`
which is a natural isomorphism `single C c j ⋙ homologyFunctor C c j ≅ 𝟭 C`.

-/

universe v u

open CategoryTheory Category Limits ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

namespace HomologicalComplex

variable (A : C)

-- INSTANCE (free from Core): (i

lemma exactAt_single_obj (A : C) (i : ι) (hi : i ≠ j) :
    ExactAt ((single C c j).obj A) i :=
  ShortComplex.exact_of_isZero_X₂ _ (isZero_single_obj_X c _ _ _ hi)

lemma isZero_single_obj_homology (A : C) (i : ι) (hi : i ≠ j) :
    IsZero (((single C c j).obj A).homology i) := by
  simpa only [← exactAt_iff_isZero_homology]
    using exactAt_single_obj c j A i hi

noncomputable def singleObjCyclesSelfIso :
    ((single C c j).obj A).cycles j ≅ A :=
  ((single C c j).obj A).iCyclesIso j _ rfl rfl ≪≫ singleObjXSelf c j A
