/-
Extracted from RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean
Genuine: 17 of 20 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!
# # Integral closure as a characteristic predicate

We prove basic properties of `IsIntegralClosure`.

-/

open Module Polynomial Submodule

section inv

open Algebra

variable {R S : Type*}

-- DISSOLVED: IsIntegral.isUnit

theorem isField_of_isIntegral_of_isField' [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] (hR : IsField R) : IsField S where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    letI := hR.toField
    obtain ⟨y, rfl⟩ := (Algebra.IsIntegral.isIntegral (R := R) x).isUnit hx
    exact ⟨y.inv, y.val_inv⟩

variable [Field R] [DivisionRing S] [Algebra R S] {x : S} {A : Subalgebra R S}

theorem IsIntegral.inv_mem_adjoin (int : IsIntegral R x) : x⁻¹ ∈ R[x] := by
  obtain rfl | h0 := eq_or_ne x 0
  · rw [inv_zero]; exact Subalgebra.zero_mem _
  have : FiniteDimensional R (R[x]) := .of_fg int.fg_adjoin_singleton
  obtain ⟨⟨y, hy⟩, h1⟩ := FiniteDimensional.exists_mul_eq_one R
    (K := R[x]) (x := ⟨x, subset_adjoin rfl⟩) (mt Subtype.ext_iff.mp h0)
  rwa [← mul_left_cancel₀ h0 ((Subtype.ext_iff.mp h1).trans (mul_inv_cancel₀ h0).symm)]

theorem IsIntegral.inv_mem (int : IsIntegral R x) (hx : x ∈ A) : x⁻¹ ∈ A :=
  adjoin_le (Set.singleton_subset_iff.mpr hx) int.inv_mem_adjoin

theorem Algebra.IsIntegral.inv_mem [Algebra.IsIntegral R A] (hx : x ∈ A) : x⁻¹ ∈ A :=
  ((isIntegral_algHom_iff A.val Subtype.val_injective).mpr <|
    Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : A)).inv_mem hx

theorem IsIntegral.inv (int : IsIntegral R x) : IsIntegral R x⁻¹ :=
  .of_mem_of_fg _ int.fg_adjoin_singleton _ int.inv_mem_adjoin

theorem IsIntegral.mem_of_inv_mem (int : IsIntegral R x) (inv_mem : x⁻¹ ∈ A) : x ∈ A := by
  rw [← inv_inv x]; exact int.inv.inv_mem inv_mem

end inv

variable {R A B S : Type*}

variable [CommRing R] [CommRing A] [Ring B] [CommRing S]

variable [Algebra R A] [Algebra R B] {f : R →+* S}

theorem Algebra.finite_iff_isIntegral_and_finiteType :
    Module.Finite R A ↔ Algebra.IsIntegral R A ∧ Algebra.FiniteType R A :=
  ⟨fun _ ↦ ⟨⟨.of_finite R⟩, inferInstance⟩, fun ⟨h, _⟩ ↦ h.finite⟩

alias RingHom.Finite.of_isIntegral_of_finiteType := RingHom.IsIntegral.to_finite

theorem RingHom.finite_iff_isIntegral_and_finiteType : f.Finite ↔ f.IsIntegral ∧ f.FiniteType :=
  ⟨fun h ↦ ⟨h.to_isIntegral, h.to_finiteType⟩, fun ⟨h, h'⟩ ↦ h.to_finite h'⟩

variable (f : R →+* S) (R A)

theorem mem_integralClosure_iff_mem_fg {r : A} :
    r ∈ integralClosure R A ↔ ∃ M : Subalgebra R A, M.toSubmodule.FG ∧ r ∈ M :=
  ⟨fun hr =>
    ⟨Algebra.adjoin R {r}, hr.fg_adjoin_singleton, Algebra.subset_adjoin rfl⟩,
    fun ⟨M, Hf, hrM⟩ => .of_mem_of_fg M Hf _ hrM⟩

variable {R A}

theorem adjoin_le_integralClosure {x : A} (hx : IsIntegral R x) :
    Algebra.adjoin R {x} ≤ integralClosure R A := by
  rw [Algebra.adjoin_le_iff]
  simp only [SetLike.mem_coe, Set.singleton_subset_iff]
  exact hx

theorem le_integralClosure_iff_isIntegral {S : Subalgebra R A} :
    S ≤ integralClosure R A ↔ Algebra.IsIntegral R S :=
  SetLike.forall.symm.trans <|
    (forall_congr' fun x =>
      show IsIntegral R (algebraMap S A x) ↔ IsIntegral R x from
        isIntegral_algebraMap_iff Subtype.coe_injective).trans
      Algebra.isIntegral_def.symm

theorem Algebra.IsIntegral.adjoin {S : Set A} (hS : ∀ x ∈ S, IsIntegral R x) :
    Algebra.IsIntegral R (adjoin R S) :=
  le_integralClosure_iff_isIntegral.mp <| adjoin_le hS

theorem integralClosure_eq_top_iff : integralClosure R A = ⊤ ↔ Algebra.IsIntegral R A := by
  rw [← top_le_iff, le_integralClosure_iff_isIntegral,
      (Subalgebra.topEquiv (R := R) (A := A)).isIntegral_iff] -- explicit arguments for speedup

theorem Algebra.isIntegral_sup {S T : Subalgebra R A} :
    Algebra.IsIntegral R (S ⊔ T : Subalgebra R A) ↔
      Algebra.IsIntegral R S ∧ Algebra.IsIntegral R T := by
  simp_rw [← le_integralClosure_iff_isIntegral, sup_le_iff]

theorem Algebra.isIntegral_iSup {ι} (S : ι → Subalgebra R A) :
    Algebra.IsIntegral R ↑(iSup S) ↔ ∀ i, Algebra.IsIntegral R (S i) := by
  simp_rw [← le_integralClosure_iff_isIntegral, iSup_le_iff]

theorem integralClosure_map_algEquiv [Algebra R S] (f : A ≃ₐ[R] S) :
    (integralClosure R A).map (f : A →ₐ[R] S) = integralClosure R S := by
  ext y
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.map f
  · intro hy
    use f.symm y, hy.map (f.symm : S →ₐ[R] A)
    simp

def AlgHom.mapIntegralClosure [Algebra R S] (f : A →ₐ[R] S) :
    integralClosure R A →ₐ[R] integralClosure R S :=
  (f.restrictDomain (integralClosure R A)).codRestrict (integralClosure R S) (fun ⟨_, h⟩ => h.map f)
