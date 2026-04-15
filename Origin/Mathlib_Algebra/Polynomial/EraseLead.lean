/-
Extracted from Algebra/Polynomial/EraseLead.lean
Genuine: 32 | Conflates: 0 | Dissolved: 19 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Monomial

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `eraseLead f`: the polynomial `f - leading term of f`

`eraseLead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/

noncomputable section

open Polynomial

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

def eraseLead (f : R[X]) : R[X] :=
  Polynomial.erase f.natDegree f

section EraseLead

theorem eraseLead_support (f : R[X]) : f.eraseLead.support = f.support.erase f.natDegree := by
  simp only [eraseLead, support_erase]

theorem eraseLead_coeff (i : ℕ) :
    f.eraseLead.coeff i = if i = f.natDegree then 0 else f.coeff i := by
  simp only [eraseLead, coeff_erase]

@[simp]
theorem eraseLead_coeff_natDegree : f.eraseLead.coeff f.natDegree = 0 := by simp [eraseLead_coeff]

theorem eraseLead_coeff_of_ne (i : ℕ) (hi : i ≠ f.natDegree) : f.eraseLead.coeff i = f.coeff i := by
  simp [eraseLead_coeff, hi]

@[simp]
theorem eraseLead_zero : eraseLead (0 : R[X]) = 0 := by simp only [eraseLead, erase_zero]

@[simp]
theorem eraseLead_add_monomial_natDegree_leadingCoeff (f : R[X]) :
    f.eraseLead + monomial f.natDegree f.leadingCoeff = f :=
  (add_comm _ _).trans (f.monomial_add_erase _)

@[simp]
theorem eraseLead_add_C_mul_X_pow (f : R[X]) :
    f.eraseLead + C f.leadingCoeff * X ^ f.natDegree = f := by
  rw [C_mul_X_pow_eq_monomial, eraseLead_add_monomial_natDegree_leadingCoeff]

@[simp]
theorem self_sub_monomial_natDegree_leadingCoeff {R : Type*} [Ring R] (f : R[X]) :
    f - monomial f.natDegree f.leadingCoeff = f.eraseLead :=
  (eq_sub_iff_add_eq.mpr (eraseLead_add_monomial_natDegree_leadingCoeff f)).symm

@[simp]
theorem self_sub_C_mul_X_pow {R : Type*} [Ring R] (f : R[X]) :
    f - C f.leadingCoeff * X ^ f.natDegree = f.eraseLead := by
  rw [C_mul_X_pow_eq_monomial, self_sub_monomial_natDegree_leadingCoeff]

-- DISSOLVED: eraseLead_ne_zero

theorem lt_natDegree_of_mem_eraseLead_support {a : ℕ} (h : a ∈ (eraseLead f).support) :
    a < f.natDegree := by
  rw [eraseLead_support, mem_erase] at h
  exact (le_natDegree_of_mem_supp a h.2).lt_of_ne h.1

theorem ne_natDegree_of_mem_eraseLead_support {a : ℕ} (h : a ∈ (eraseLead f).support) :
    a ≠ f.natDegree :=
  (lt_natDegree_of_mem_eraseLead_support h).ne

theorem natDegree_not_mem_eraseLead_support : f.natDegree ∉ (eraseLead f).support := fun h =>
  ne_natDegree_of_mem_eraseLead_support h rfl

-- DISSOLVED: eraseLead_support_card_lt

-- DISSOLVED: card_support_eraseLead_add_one

@[simp]
theorem card_support_eraseLead : #f.eraseLead.support = #f.support - 1 := by
  by_cases hf : f = 0
  · rw [hf, eraseLead_zero, support_zero, card_empty]
  · rw [← card_support_eraseLead_add_one hf, add_tsub_cancel_right]

theorem card_support_eraseLead' {c : ℕ} (fc : #f.support = c + 1) :
    #f.eraseLead.support = c := by
  rw [card_support_eraseLead, fc, add_tsub_cancel_right]

-- DISSOLVED: card_support_eq_one_of_eraseLead_eq_zero

theorem card_support_le_one_of_eraseLead_eq_zero (h : f.eraseLead = 0) : #f.support ≤ 1 := by
  by_cases hpz : f = 0
  case pos => simp [hpz]
  case neg => exact le_of_eq (card_support_eq_one_of_eraseLead_eq_zero hpz h)

@[simp]
theorem eraseLead_monomial (i : ℕ) (r : R) : eraseLead (monomial i r) = 0 := by
  classical
  by_cases hr : r = 0
  · subst r
    simp only [monomial_zero_right, eraseLead_zero]
  · rw [eraseLead, natDegree_monomial, if_neg hr, erase_monomial]

@[simp]
theorem eraseLead_C (r : R) : eraseLead (C r) = 0 :=
  eraseLead_monomial _ _

@[simp]
theorem eraseLead_X : eraseLead (X : R[X]) = 0 :=
  eraseLead_monomial _ _

@[simp]
theorem eraseLead_X_pow (n : ℕ) : eraseLead (X ^ n : R[X]) = 0 := by
  rw [X_pow_eq_monomial, eraseLead_monomial]

@[simp]
theorem eraseLead_C_mul_X_pow (r : R) (n : ℕ) : eraseLead (C r * X ^ n) = 0 := by
  rw [C_mul_X_pow_eq_monomial, eraseLead_monomial]

@[simp] lemma eraseLead_C_mul_X (r : R) : eraseLead (C r * X) = 0 := by
  simpa using eraseLead_C_mul_X_pow _ 1

theorem eraseLead_add_of_degree_lt_left {p q : R[X]} (pq : q.degree < p.degree) :
    (p + q).eraseLead = p.eraseLead + q := by
  ext n
  by_cases nd : n = p.natDegree
  · rw [nd, eraseLead_coeff, if_pos (natDegree_add_eq_left_of_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq degree_le_natDegree)).symm
  · rw [eraseLead_coeff, coeff_add, coeff_add, eraseLead_coeff, if_neg, if_neg nd]
    rintro rfl
    exact nd (natDegree_add_eq_left_of_degree_lt pq)

theorem eraseLead_add_of_natDegree_lt_left {p q : R[X]} (pq : q.natDegree < p.natDegree) :
    (p + q).eraseLead = p.eraseLead + q :=
  eraseLead_add_of_degree_lt_left (degree_lt_degree pq)

theorem eraseLead_add_of_degree_lt_right {p q : R[X]} (pq : p.degree < q.degree) :
    (p + q).eraseLead = p + q.eraseLead := by
  ext n
  by_cases nd : n = q.natDegree
  · rw [nd, eraseLead_coeff, if_pos (natDegree_add_eq_right_of_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq degree_le_natDegree)).symm
  · rw [eraseLead_coeff, coeff_add, coeff_add, eraseLead_coeff, if_neg, if_neg nd]
    rintro rfl
    exact nd (natDegree_add_eq_right_of_degree_lt pq)

theorem eraseLead_add_of_natDegree_lt_right {p q : R[X]} (pq : p.natDegree < q.natDegree) :
    (p + q).eraseLead = p + q.eraseLead :=
  eraseLead_add_of_degree_lt_right (degree_lt_degree pq)

theorem eraseLead_degree_le : (eraseLead f).degree ≤ f.degree :=
  f.degree_erase_le _

-- DISSOLVED: degree_eraseLead_lt

theorem eraseLead_natDegree_le_aux : (eraseLead f).natDegree ≤ f.natDegree :=
  natDegree_le_natDegree eraseLead_degree_le

theorem eraseLead_natDegree_lt (f0 : 2 ≤ #f.support) : (eraseLead f).natDegree < f.natDegree :=
  lt_of_le_of_ne eraseLead_natDegree_le_aux <|
    ne_natDegree_of_mem_eraseLead_support <|
      natDegree_mem_support_of_nonzero <| eraseLead_ne_zero f0

-- DISSOLVED: natDegree_pos_of_eraseLead_ne_zero

theorem eraseLead_natDegree_lt_or_eraseLead_eq_zero (f : R[X]) :
    (eraseLead f).natDegree < f.natDegree ∨ f.eraseLead = 0 := by
  by_cases h : #f.support ≤ 1
  · right
    rw [← C_mul_X_pow_eq_self h]
    simp
  · left
    apply eraseLead_natDegree_lt (lt_of_not_ge h)

theorem eraseLead_natDegree_le (f : R[X]) : (eraseLead f).natDegree ≤ f.natDegree - 1 := by
  rcases f.eraseLead_natDegree_lt_or_eraseLead_eq_zero with (h | h)
  · exact Nat.le_sub_one_of_lt h
  · simp only [h, natDegree_zero, zero_le]

-- DISSOLVED: natDegree_eraseLead

-- DISSOLVED: natDegree_eraseLead_add_one

theorem natDegree_eraseLead_le_of_nextCoeff_eq_zero (h : f.nextCoeff = 0) :
    f.eraseLead.natDegree ≤ f.natDegree - 2 := by
  refine natDegree_le_pred (n := f.natDegree - 1) (eraseLead_natDegree_le f) ?_
  rw [nextCoeff_eq_zero, natDegree_eq_zero] at h
  obtain ⟨a, rfl⟩ | ⟨hf, h⟩ := h
  · simp
  rw [eraseLead_coeff_of_ne _ (tsub_lt_self hf zero_lt_one).ne, ← nextCoeff_of_natDegree_pos hf]
  simp [nextCoeff_eq_zero, h, eq_zero_or_pos]

-- DISSOLVED: two_le_natDegree_of_nextCoeff_eraseLead

-- DISSOLVED: leadingCoeff_eraseLead_eq_nextCoeff

theorem nextCoeff_eq_zero_of_eraseLead_eq_zero (h : f.eraseLead = 0) : f.nextCoeff = 0 := by
  by_contra h₂
  exact leadingCoeff_ne_zero.mp (leadingCoeff_eraseLead_eq_nextCoeff h₂ ▸ h₂) h

end EraseLead

-- DISSOLVED: induction_with_natDegree_le

-- DISSOLVED: mono_map_natDegree_eq

-- DISSOLVED: map_natDegree_eq_sub

-- DISSOLVED: map_natDegree_eq_natDegree

-- DISSOLVED: card_support_eq'

-- DISSOLVED: card_support_eq

-- DISSOLVED: card_support_eq_one

-- DISSOLVED: card_support_eq_two

-- DISSOLVED: card_support_eq_three

end Polynomial
