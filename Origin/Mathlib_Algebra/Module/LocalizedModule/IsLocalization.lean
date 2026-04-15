/-
Extracted from Algebra/Module/LocalizedModule/IsLocalization.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Equivalence between `IsLocalizedModule` and `IsLocalization`
-/

section IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

variable {A Aₛ : Type*} [CommSemiring A] [Algebra R A]

variable [CommSemiring Aₛ] [Algebra A Aₛ] [Algebra R Aₛ] [IsScalarTower R A Aₛ]

variable {S} in

theorem isLocalizedModule_iff_isLocalization :
    IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔
      IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ := by
  rw [isLocalizedModule_iff, isLocalization_iff]
  refine and_congr ?_ (and_congr (forall_congr' fun _ ↦ ?_) (forall₂_congr fun _ _ ↦ ?_))
  · simp_rw [← (Algebra.lmul R Aₛ).commutes, Algebra.lmul_isUnit_iff, Subtype.forall,
      Algebra.algebraMapSubmonoid, ← SetLike.mem_coe, Submonoid.coe_map,
      Set.forall_mem_image, ← IsScalarTower.algebraMap_apply]
  · simp_rw [Prod.exists, Subtype.exists, Algebra.algebraMapSubmonoid]
    simp [← IsScalarTower.algebraMap_apply, Submonoid.mk_smul, Algebra.smul_def, mul_comm]
  · congr!; simp_rw [Subtype.exists, Algebra.algebraMapSubmonoid]; simp [Algebra.smul_def]

-- INSTANCE (free from Core): [IsLocalization

variable (A)

lemma isLocalizedModule_iff_isLocalization' :
    IsLocalizedModule S (Algebra.linearMap R A) ↔ IsLocalization S A := by
  convert isLocalizedModule_iff_isLocalization (S := S) (A := R) (Aₛ := A)
  exact (Submonoid.map_id S).symm

-- INSTANCE (free from Core): [IsLocalization

variable {S A} in

lemma IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]
    {x : A} {s : S} : IsLocalization.mk' Aₛ x ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem s⟩ =
      IsLocalizedModule.mk' (IsScalarTower.toAlgHom R A Aₛ).toLinearMap x s := by
  rw [← IsLocalizedModule.smul_inj (IsScalarTower.toAlgHom R A Aₛ).toLinearMap s,
    IsLocalizedModule.mk'_cancel', Submonoid.smul_def, ← algebraMap_smul A]
  exact IsLocalization.smul_mk'_self (m := ⟨_, _⟩)

lemma IsLocalization.mk'_eq_mk' [IsLocalization S A] (x : R) (s : S) :
    IsLocalization.mk' A x s = IsLocalizedModule.mk' (Algebra.linearMap R A) x s := by
  rw [← IsLocalizedModule.smul_inj (Algebra.linearMap R A) s, IsLocalizedModule.mk'_cancel']
  exact IsLocalization.smul_mk'_self

end IsLocalizedModule
