/-
Extracted from Analysis/CStarAlgebra/Unitary/Span.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Unitary elements span C⋆-algebras

## Main results

+ `CStarAlgebra.exists_sum_four_unitary`: every element `x` in a unital C⋆-algebra is a linear
  combination of four unitary elements, and the norm of each coefficient does not exceed `‖x‖ / 2`.
+ `CStarAlgebra.span_unitary`: a unital C⋆-algebra is spanned by its unitary elements.
-/

variable {A : Type*} [CStarAlgebra A]

open scoped ComplexStarModule

open Complex

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

set_option backward.isDefEq.respectTransparency false in

lemma IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary (a : A) (ha : IsSelfAdjoint a)
    (ha_norm : ‖a‖ ≤ 1) : a + I • CFC.sqrt (1 - a ^ 2) ∈ unitary A := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim (a + I • CFC.sqrt (1 - a ^ 2)) 1, one_mem (unitary A)]
  have key : a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x : ℂ ↦ x.re + I * √(1 - x.re ^ 2)) a := by
    rw [CFC.sqrt_eq_real_sqrt (1 - a ^ 2) ?nonneg]
    case nonneg =>
      rwa [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (a ^ 2), sq, ha.norm_mul_self,
        sq_le_one_iff₀ (by positivity)]
    rw [cfc_add .., cfc_const_mul .., ← cfc_real_eq_complex (fun x ↦ x) ha, cfc_id' ℝ a,
      ← cfc_real_eq_complex (fun x ↦ √(1 - x ^ 2)) ha, cfcₙ_eq_cfc, cfc_comp' (√·) (1 - · ^ 2) a,
      cfc_sub .., cfc_pow .., cfc_const_one .., cfc_id' ..]
  rw [key, cfc_unitary_iff ..]
  intro x hx
  rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_ofReal_add_I_mul_sqrt_one_sub, Complex.ofReal_one]
  exact spectrum.norm_le_norm_of_mem (ha.spectrumRestricts.apply_mem hx) |>.trans ha_norm
