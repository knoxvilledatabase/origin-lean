/-
Extracted from Algebra/Homology/HomotopyCategory/SingleFunctors.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Single functors from the homotopy category

Let `C` be a preadditive category with a zero object.
In this file, we put together all the single functors `C ⥤ CochainComplex C ℤ`
along with their compatibilities with shifts into the definition
`CochainComplex.singleFunctors C : SingleFunctors C (CochainComplex C ℤ) ℤ`.
Similarly, we define
`HomotopyCategory.singleFunctors C : SingleFunctors C (HomotopyCategory C (ComplexShape.up ℤ)) ℤ`.

-/

assert_not_exists TwoSidedIdeal

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
        obtain rfl : a' = a + n := by lia
        by_cases h : i = a
        · subst h
          simp only [Functor.comp_obj, shiftFunctor_obj_X', single_obj_X_self]
        · dsimp [single]
          rw [if_neg h, if_neg (fun h' => h (by lia))])))
    (fun {X Y} f => by
      obtain rfl : a' = a + n := by lia
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

-- INSTANCE (free from Core): (n

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (R

noncomputable abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

variable {C} in
