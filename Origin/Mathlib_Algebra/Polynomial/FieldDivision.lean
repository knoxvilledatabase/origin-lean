/-
Extracted from Algebra/Polynomial/FieldDivision.lean
Genuine: 5 of 17 | Dissolved: 11 | Infrastructure: 1
-/
import Origin.Core

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $R[X]$

-/

noncomputable section

open Polynomial

open scoped Nat

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R]

-- DISSOLVED: rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero

theorem derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} (hpt : Polynomial.IsRoot p t)
    (hnzd : (p.rootMultiplicity t : R) ∈ nonZeroDivisors R) :
    (derivative p).rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · simp only [h, map_zero, rootMultiplicity_zero]
  obtain ⟨g, hp, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h t
  set m := p.rootMultiplicity t
  have hm : m - 1 + 1 = m := Nat.sub_add_cancel <| (rootMultiplicity_pos h).2 hpt
  have hndvd : ¬(X - C t) ^ m ∣ derivative p := by
    rw [hp, derivative_mul, dvd_add_left (dvd_mul_right _ _),
      derivative_X_sub_C_pow, ← hm, pow_succ, hm, mul_comm (C _), mul_assoc,
      dvd_cancel_left_mem_nonZeroDivisors (monic_X_sub_C t |>.pow _ |>.mem_nonZeroDivisors)]
    rw [dvd_iff_isRoot, IsRoot] at hndvd ⊢
    rwa [eval_mul, eval_C, mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd]
  have hnezero : derivative p ≠ 0 := fun h ↦ hndvd (by rw [h]; exact dvd_zero _)
  exact le_antisymm (by rwa [rootMultiplicity_le_iff hnezero, hm])
    (rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero _ t hnezero)

theorem isRoot_iterate_derivative_of_lt_rootMultiplicity {p : R[X]} {t : R} {n : ℕ}
    (hn : n < p.rootMultiplicity t) : (derivative^[n] p).IsRoot t :=
  dvd_iff_isRoot.mp <| (dvd_pow_self _ <| Nat.sub_ne_zero_of_lt hn).trans
    (pow_sub_dvd_iterate_derivative_of_pow_dvd _ <| p.pow_rootMultiplicity_dvd t)

open Finset in

theorem eval_iterate_derivative_rootMultiplicity {p : R[X]} {t : R} :
    (derivative^[p.rootMultiplicity t] p).eval t =
      (p.rootMultiplicity t).factorial • (p /ₘ (X - C t) ^ p.rootMultiplicity t).eval t := by
  set m := p.rootMultiplicity t with hm
  conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq t, ← hm]
  rw [iterate_derivative_mul, eval_finset_sum, sum_eq_single_of_mem _ (mem_range.mpr m.succ_pos)]
  · rw [m.choose_zero_right, one_smul, eval_mul, m.sub_zero, iterate_derivative_X_sub_pow_self,
      eval_natCast, nsmul_eq_mul]; rfl
  · intro b hb hb0
    rw [iterate_derivative_X_sub_pow, eval_smul, eval_mul, eval_smul, eval_pow,
      Nat.sub_sub_self (mem_range_succ_iff.mp hb), eval_sub, eval_X, eval_C, sub_self,
      zero_pow hb0, smul_zero, zero_mul, smul_zero]

-- DISSOLVED: lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors

-- DISSOLVED: lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'

-- DISSOLVED: lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors

-- DISSOLVED: lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'

-- DISSOLVED: one_lt_rootMultiplicity_iff_isRoot_iterate_derivative

-- DISSOLVED: one_lt_rootMultiplicity_iff_isRoot

end CommRing

section IsDomain

variable [CommRing R]

-- DISSOLVED: one_lt_rootMultiplicity_iff_isRoot_gcd

variable [NoZeroDivisors R]

theorem derivative_rootMultiplicity_of_root [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t) :
    p.derivative.rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · rw [h, map_zero, rootMultiplicity_zero]
  exact derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hpt <|
    mem_nonZeroDivisors_of_ne_zero <| Nat.cast_ne_zero.2 ((rootMultiplicity_pos h).2 hpt).ne'

theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity [CharZero R] (p : R[X]) (t : R) :
    p.rootMultiplicity t - 1 ≤ p.derivative.rootMultiplicity t := by
  by_cases h : p.IsRoot t
  · exact (derivative_rootMultiplicity_of_root h).symm.le
  · rw [rootMultiplicity_eq_zero h, zero_tsub]
    exact zero_le _

-- DISSOLVED: lt_rootMultiplicity_of_isRoot_iterate_derivative

-- DISSOLVED: lt_rootMultiplicity_iff_isRoot_iterate_derivative

-- DISSOLVED: isRoot_of_isRoot_of_dvd_derivative_mul

section NormalizationMonoid

variable [NormalizationMonoid R]

-- INSTANCE (free from Core): instNormalizationMonoid
