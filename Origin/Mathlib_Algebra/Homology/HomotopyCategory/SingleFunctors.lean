/-
Extracted from Algebra/Homology/HomotopyCategory/SingleFunctors.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.CategoryTheory.Shift.SingleFunctors

/-!
# Single functors from the homotopy category

Let `C` be a preadditive category with a zero object.
In this file, we put together all the single functors `C ⥤ CochainComplex C ℤ`
along with their compatibilities with shifts into the definition
`CochainComplex.singleFunctors C : SingleFunctors C (CochainComplex C ℤ) ℤ`.
Similarly, we define
`HomotopyCategory.singleFunctors C : SingleFunctors C (HomotopyCategory C (ComplexShape.up ℤ)) ℤ`.

-/

universe v' u' v u

open CategoryTheory Category Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CochainComplex

open HomologicalComplex

noncomputable def singleFunctors : SingleFunctors C (CochainComplex C ℤ) ℤ where
  functor n := single _ _ n
  shiftIso n a a' ha' := NatIso.ofComponents
    (fun X => Hom.isoOfComponents
      (fun i => eqToIso (by
        obtain rfl : a' = a + n := by omega
        by_cases h : i = a
        · subst h
          simp only [Functor.comp_obj, shiftFunctor_obj_X', single_obj_X_self]
        · dsimp [single]
          rw [if_neg h, if_neg (fun h' => h (by omega))])))
    (fun {X Y} f => by
      obtain rfl : a' = a + n := by omega
      ext
      simp [single])
  shiftIso_zero a := by
    ext
    dsimp
    simp only [single, shiftFunctorZero_eq, shiftFunctorZero'_hom_app_f,
      XIsoOfEq, eqToIso.hom]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext
    dsimp
    simp only [shiftFunctorAdd_eq, shiftFunctorAdd'_hom_app_f, XIsoOfEq,
      eqToIso.hom, eqToHom_trans, id_comp]

instance (n : ℤ) : ((singleFunctors C).functor n).Additive := by
  dsimp only [singleFunctors]
  infer_instance

noncomputable abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

end CochainComplex

namespace HomotopyCategory

noncomputable def singleFunctors : SingleFunctors C (HomotopyCategory C (ComplexShape.up ℤ)) ℤ :=
  (CochainComplex.singleFunctors C).postcomp (HomotopyCategory.quotient _ _)

noncomputable abbrev singleFunctor (n : ℤ) :
    C ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  (singleFunctors C).functor n

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp only [singleFunctor, singleFunctors, SingleFunctors.postcomp]
  infer_instance

noncomputable def singleFunctorsPostcompQuotientIso :
    singleFunctors C ≅
      (CochainComplex.singleFunctors C).postcomp (HomotopyCategory.quotient _ _) :=
  Iso.refl _

noncomputable def singleFunctorPostcompQuotientIso (n : ℤ) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ quotient _ _ :=
  (SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostcompQuotientIso C)

end HomotopyCategory
