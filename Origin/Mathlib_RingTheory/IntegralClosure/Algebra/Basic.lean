/-
Extracted from RingTheory/IntegralClosure/Algebra/Basic.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Integral closure of a subring.

Let `A` be an `R`-algebra. We prove that integral elements form a sub-`R`-algebra of `A`.

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `integralClosure R A` : the integral closure of `R` in an `R`-algebra `A`.
-/

open Polynomial Submodule

variable {R A B S : Type*}

variable [CommRing R] [CommRing A] [Ring B] [CommRing S]

variable [Algebra R A] [Algebra R B] (f : R →+* S)

theorem Subalgebra.isIntegral_iff (S : Subalgebra R B) :
    Algebra.IsIntegral R S ↔ ∀ x ∈ S, IsIntegral R x :=
  Algebra.isIntegral_def.trans <| .trans
    (forall_congr' fun _ ↦ (isIntegral_algHom_iff S.val Subtype.val_injective).symm) Subtype.forall

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

theorem Algebra.IsIntegral.of_injective (f : A →ₐ[R] B) (hf : Function.Injective f)
    [Algebra.IsIntegral R B] : Algebra.IsIntegral R A :=
  ⟨fun _ ↦ (isIntegral_algHom_iff f hf).mp (isIntegral _)⟩

theorem Algebra.IsIntegral.of_surjective [Algebra.IsIntegral R A]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) : Algebra.IsIntegral R B :=
  isIntegral_def.mpr fun b ↦ let ⟨a, ha⟩ := hf b; ha ▸ (isIntegral_def.mp ‹_› a).map f

theorem AlgEquiv.isIntegral_iff (e : A ≃ₐ[R] B) : Algebra.IsIntegral R A ↔ Algebra.IsIntegral R B :=
  ⟨fun h ↦ h.of_injective e.symm e.symm.injective, fun h ↦ h.of_injective e e.injective⟩

end

-- INSTANCE (free from Core): Module.End.isIntegral

variable (R) in
