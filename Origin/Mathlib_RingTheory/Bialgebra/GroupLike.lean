/-
Extracted from RingTheory/Bialgebra/GroupLike.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Group-like elements in a bialgebra

This file proves that group-like elements in a bialgebra form a monoid.
-/

open Coalgebra Bialgebra

variable {R A : Type*}

section Semiring

variable [CommSemiring R] [Semiring A] [Bialgebra R A] {a b : A}

lemma IsGroupLikeElem.one : IsGroupLikeElem R (1 : A) where
  counit_eq_one := counit_one
  comul_eq_tmul_self := comul_one

lemma IsGroupLikeElem.mul (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b) :
    IsGroupLikeElem R (a * b) where
  counit_eq_one := by simp [ha, hb]
  comul_eq_tmul_self := by simp [ha, hb]

variable (R A) in

def groupLikeSubmonoid : Submonoid A where
  carrier := {a | IsGroupLikeElem R a}
  one_mem' := .one
  mul_mem' := .mul

lemma IsGroupLikeElem.pow {n : ℕ} (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (a ^ n) :=
  (groupLikeSubmonoid R A).pow_mem ha _

lemma IsGroupLikeElem.of_mul_eq_one (hab : a * b = 1) (hba : b * a = 1) (ha : IsGroupLikeElem R a) :
    IsGroupLikeElem R b where
  counit_eq_one :=
    left_inv_eq_right_inv (a := counit a) (by simp [← counit_mul, hba]) (by simp [ha])
  comul_eq_tmul_self := left_inv_eq_right_inv (a := comul a) (by simp [← comul_mul, hba])
    (by simp [ha, hab, Algebra.TensorProduct.one_def])

lemma isGroupLikeElem_iff_of_mul_eq_one (hab : a * b = 1) (hba : b * a = 1) :
    IsGroupLikeElem R a ↔ IsGroupLikeElem R b := ⟨.of_mul_eq_one hab hba, .of_mul_eq_one hba hab⟩
