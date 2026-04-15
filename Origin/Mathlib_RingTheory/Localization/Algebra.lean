/-
Extracted from RingTheory/Localization/Algebra.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Localization of algebra maps

In this file we provide constructors to localize algebra maps. Also we show that
localization commutes with taking kernels for ring homomorphisms.

## Implementation detail

The proof that localization commutes with taking kernels does not use the result for linear maps,
as the translation is currently tedious and can be unified easily after the localization refactor.

-/

variable {R S P : Type*} (Q : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]
  [CommSemiring Q]
  {M : Submonoid R} {T : Submonoid P}
  [Algebra R S] [Algebra P Q] [IsLocalization M S] [IsLocalization T Q]
  (g : R →+* P)

open IsLocalization in

variable (M S) in

-- INSTANCE (free from Core): Algebra.idealMap_isLocalizedModule

lemma IsLocalization.ker_map (hT : Submonoid.map g M = T) :
    RingHom.ker (IsLocalization.map Q g (hT.symm ▸ M.le_comap_map) : S →+* Q) =
      (RingHom.ker g).map (algebraMap R S) := by
  ext x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp [RingHom.mem_ker, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff, ← hT]

variable (S) in

noncomputable def RingHom.toKerIsLocalization (hy : M ≤ Submonoid.comap g T) :
    RingHom.ker g →ₗ[R] RingHom.ker (IsLocalization.map Q g hy : S →+* Q) where
  toFun x := ⟨algebraMap R S x, by simp [RingHom.mem_ker, RingHom.mem_ker.mp x.property]⟩
  map_add' x y := by
    simp only [Submodule.coe_add, map_add, AddMemClass.mk_add_mk]
  map_smul' a x := by
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, id_apply, SetLike.mk_smul_of_tower_mk,
      Algebra.smul_def]
