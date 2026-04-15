/-
Extracted from Algebra/Polynomial/Degree/SmallDegree.lean
Genuine: 15 | Conflates: 0 | Dissolved: 13 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Nat.WithBot

/-!
# Results on polynomials of specific small degrees
-/

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

theorem eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) : p = C (p.coeff 1) * X + C (p.coeff 0) :=
  ext fun n =>
    Nat.casesOn n (by simp) fun n =>
      Nat.casesOn n (by simp [coeff_C]) fun m => by
        -- Porting note: `by decide` → `Iff.mpr ..`
        have : degree p < m.succ.succ := lt_of_le_of_lt h
          (Iff.mpr WithBot.coe_lt_coe <| Nat.succ_lt_succ <| Nat.zero_lt_succ m)
        simp [coeff_eq_zero_of_degree_lt this, coeff_C, Nat.succ_ne_zero, coeff_X, Nat.succ_inj',
          @eq_comm ℕ 0]

theorem eq_X_add_C_of_degree_eq_one (h : degree p = 1) :
    p = C p.leadingCoeff * X + C (p.coeff 0) :=
  (eq_X_add_C_of_degree_le_one h.le).trans
    (by rw [← Nat.cast_one] at h; rw [leadingCoeff, natDegree_eq_of_degree_eq_some h])

theorem eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) :
    p = C (p.coeff 1) * X + C (p.coeff 0) :=
  eq_X_add_C_of_degree_le_one <| degree_le_of_natDegree_le h

theorem Monic.eq_X_add_C (hm : p.Monic) (hnd : p.natDegree = 1) : p = X + C (p.coeff 0) := by
  rw [← one_mul X, ← C_1, ← hm.coeff_natDegree, hnd, ← eq_X_add_C_of_natDegree_le_one hnd.le]

theorem exists_eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) : ∃ a b, p = C a * X + C b :=
  ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one h⟩

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

-- DISSOLVED: zero_le_degree_iff

-- DISSOLVED: ne_zero_of_coe_le_degree

theorem le_natDegree_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : n ≤ p.natDegree :=
  -- Porting note: `.. ▸ ..` → `rwa [..] at ..`
  WithBot.coe_le_coe.mp <| by
    rwa [degree_eq_natDegree <| ne_zero_of_coe_le_degree hdeg] at hdeg

theorem degree_linear_le : degree (C a * X + C b) ≤ 1 :=
  degree_add_le_of_degree_le (degree_C_mul_X_le _) <| le_trans degree_C_le Nat.WithBot.coe_nonneg

theorem degree_linear_lt : degree (C a * X + C b) < 2 :=
  degree_linear_le.trans_lt <| WithBot.coe_lt_coe.mpr one_lt_two

-- DISSOLVED: degree_linear

theorem natDegree_linear_le : natDegree (C a * X + C b) ≤ 1 :=
  natDegree_le_of_degree_le degree_linear_le

-- DISSOLVED: natDegree_linear

-- DISSOLVED: leadingCoeff_linear

theorem degree_quadratic_le : degree (C a * X ^ 2 + C b * X + C c) ≤ 2 := by
  simpa only [add_assoc] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 2 a)
      (le_trans degree_linear_le <| WithBot.coe_le_coe.mpr one_le_two)

theorem degree_quadratic_lt : degree (C a * X ^ 2 + C b * X + C c) < 3 :=
  degree_quadratic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 2

-- DISSOLVED: degree_linear_lt_degree_C_mul_X_sq

-- DISSOLVED: degree_quadratic

theorem natDegree_quadratic_le : natDegree (C a * X ^ 2 + C b * X + C c) ≤ 2 :=
  natDegree_le_of_degree_le degree_quadratic_le

-- DISSOLVED: natDegree_quadratic

-- DISSOLVED: leadingCoeff_quadratic

theorem degree_cubic_le : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 := by
  simpa only [add_assoc] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 3 a)
      (le_trans degree_quadratic_le <| WithBot.coe_le_coe.mpr <| Nat.le_succ 2)

theorem degree_cubic_lt : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) < 4 :=
  degree_cubic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 3

-- DISSOLVED: degree_quadratic_lt_degree_C_mul_X_cb

-- DISSOLVED: degree_cubic

theorem natDegree_cubic_le : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 :=
  natDegree_le_of_degree_le degree_cubic_le

-- DISSOLVED: natDegree_cubic

-- DISSOLVED: leadingCoeff_cubic

end Semiring

end Polynomial
