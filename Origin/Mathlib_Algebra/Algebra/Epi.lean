/-
Extracted from Algebra/Algebra/Epi.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Algebras which are commutative ring epimorphisms
-/

noncomputable section

open Function TensorProduct

namespace Algebra

section Semiring

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

protected class IsEpi : Prop where
  injective_lift_mul : Injective <| lift <| LinearMap.mul R A

end Semiring

-- INSTANCE (free from Core): (R

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

lemma isEpi_iff_surjective_algebraMap_of_finite [Module.Finite R A] :
    Algebra.IsEpi R A ↔ Surjective (algebraMap R A) := by
  refine ⟨fun h ↦ ?_, isEpi_of_surjective_algebraMap R A⟩
  let R' := (Algebra.linearMap R A).range
  rcases subsingleton_or_nontrivial (A ⧸ R') with h | _
  · rwa [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top] at h
  have : Subsingleton ((A ⧸ R') ⊗[R] (A ⧸ R')) := by
    refine subsingleton_of_forall_eq 0 fun y ↦ ?_
    induction y with
    | zero => rfl
    | add a b e₁ e₂ => rwa [e₁, zero_add]
    | tmul x y =>
      obtain ⟨x, rfl⟩ := R'.mkQ_surjective x
      obtain ⟨y, rfl⟩ := R'.mkQ_surjective y
      obtain ⟨s, hs⟩ : ∃ s, 1 ⊗ₜ[R] s = x ⊗ₜ[R] y := by
        use x * y
        trans x ⊗ₜ 1 * 1 ⊗ₜ y
        · simp [(isEpi_iff_forall_one_tmul_eq R A).mp]
        · simp
      have : R'.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero R').mpr ⟨1, map_one (algebraMap R A)⟩
      rw [← map_tmul R'.mkQ R'.mkQ, ← hs, map_tmul, this, zero_tmul]
  cases false_of_nontrivial_of_subsingleton ((A ⧸ R') ⊗[R] (A ⧸ R'))
