/-
Extracted from CategoryTheory/Shift/SingleFunctors.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functors from a category to a category with a shift

Given a category `C`, and a category `D` equipped with a shift by a monoid `A`,
we define a structure `SingleFunctors C D A` which contains the data of
functors `functor a : C ⥤ D` for all `a : A` and isomorphisms
`shiftIso n a a' h : functor a' ⋙ shiftFunctor D n ≅ functor a`
whenever `n + a = a'`. These isomorphisms should satisfy certain compatibilities
with respect to the shift on `D`.

This notion is similar to `Functor.ShiftSequence` which can be used in order to
attach shifted versions of a homological functor `D ⥤ C` with `D` a
triangulated category and `C` an abelian category. However, the definition
`SingleFunctors` is for functors in the other direction: it is meant to
ease the formalization of the compatibilities with shifts of the
functors `C ⥤ CochainComplex C ℤ` (or `C ⥤ DerivedCategory C` (TODO))
which sends an object `X : C` to a complex where `X` sits in a single degree.

-/

open CategoryTheory Category ZeroObject Limits Functor

variable (C D E E' : Type*) [Category* C] [Category* D] [Category* E] [Category* E']
  (A : Type*) [AddMonoid A] [HasShift D A] [HasShift E A] [HasShift E' A]

namespace CategoryTheory

structure SingleFunctors where
  /-- a family of functors `C ⥤ D` indexed by the elements of the additive monoid `A` -/
  functor (a : A) : C ⥤ D
  /-- the isomorphism `functor a' ⋙ shiftFunctor D n ≅ functor a` when `n + a = a'` -/
  shiftIso (n a a' : A) (ha' : n + a = a') : functor a' ⋙ shiftFunctor D n ≅ functor a
  /-- `shiftIso 0` is the obvious isomorphism. -/
  shiftIso_zero (a : A) :
    shiftIso 0 a a (zero_add a) = isoWhiskerLeft _ (shiftFunctorZero D A)
  /-- `shiftIso (m + n)` is determined by `shiftIso m` and `shiftIso n`. -/
  shiftIso_add (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') :
    shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerLeft _ (shiftFunctorAdd D m n) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (shiftIso m a' a'' ha'') _ ≪≫ shiftIso n a a' ha'

variable {C D E A}

variable (F G H : SingleFunctors C D A)

namespace SingleFunctors

lemma shiftIso_add_hom_app (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).hom.app X =
      (shiftFunctorAdd D m n).hom.app ((F.functor a'').obj X) ≫
        ((F.shiftIso m a' a'' ha'').hom.app X)⟦n⟧' ≫
        (F.shiftIso n a a' ha').hom.app X := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

lemma shiftIso_add_inv_app (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).inv.app X =
      (F.shiftIso n a a' ha').inv.app X ≫
      ((F.shiftIso m a' a'' ha'').inv.app X)⟦n⟧' ≫
      (shiftFunctorAdd D m n).inv.app ((F.functor a'').obj X) := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

lemma shiftIso_add' (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc]) =
      isoWhiskerLeft _ (shiftFunctorAdd' D m n mn hnm) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (F.shiftIso m a' a'' ha'') _ ≪≫ F.shiftIso n a a' ha' := by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftIso_add]

lemma shiftIso_add'_hom_app (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X =
      (shiftFunctorAdd' D m n mn hnm).hom.app ((F.functor a'').obj X) ≫
        ((F.shiftIso m a' a'' ha'').hom.app X)⟦n⟧' ≫ (F.shiftIso n a a' ha').hom.app X := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

lemma shiftIso_add'_inv_app (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).inv.app X =
      (F.shiftIso n a a' ha').inv.app X ≫
      ((F.shiftIso m a' a'' ha'').inv.app X)⟦n⟧' ≫
      (shiftFunctorAdd' D m n mn hnm).inv.app ((F.functor a'').obj X) := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']
