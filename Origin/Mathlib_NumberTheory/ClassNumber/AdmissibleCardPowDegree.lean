/-
Extracted from NumberTheory/ClassNumber/AdmissibleCardPowDegree.lean
Genuine: 4 of 7 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.Degree.CardPowDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Admissible absolute values on polynomials

This file defines an admissible absolute value `Polynomial.cardPowDegreeIsAdmissible` which we
use to show the class number of the ring of integers of a function field is finite.

## Main results

* `Polynomial.cardPowDegreeIsAdmissible` shows `cardPowDegree`,
  mapping `p : Polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/

namespace Polynomial

open AbsoluteValue Real

variable {Fq : Type*} [Fintype Fq]

theorem exists_eq_polynomial [Semiring Fq] {d : ℕ} {m : ℕ} (hm : Fintype.card Fq ^ d ≤ m)
    (b : Fq[X]) (hb : natDegree b ≤ d) (A : Fin m.succ → Fq[X])
    (hA : ∀ i, degree (A i) < degree b) : ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₁ = A i₀ := by
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `0`, ... `degree b - 1` ≤ `d - 1`.
  -- In other words, the following map is not injective:
  set f : Fin m.succ → Fin d → Fq := fun i j => (A i).coeff j
  have : Fintype.card (Fin d → Fq) < Fintype.card (Fin m.succ) := by
    simpa using lt_of_le_of_lt hm (Nat.lt_succ_self m)
  -- Therefore, the differences have all coefficients higher than `deg b - d` equal.
  obtain ⟨i₀, i₁, i_ne, i_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f this
  use i₀, i₁, i_ne
  ext j
  -- The coefficients higher than `deg b` are the same because they are equal to 0.
  by_cases hbj : degree b ≤ j
  · rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj),
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj)]
  -- So we only need to look for the coefficients between `0` and `deg b`.
  rw [not_le] at hbj
  apply congr_fun i_eq.symm ⟨j, _⟩
  exact lt_of_lt_of_le (coe_lt_degree.mp hbj) hb

theorem exists_approx_polynomial_aux [Ring Fq] {d : ℕ} {m : ℕ} (hm : Fintype.card Fq ^ d ≤ m)
    (b : Fq[X]) (A : Fin m.succ → Fq[X]) (hA : ∀ i, degree (A i) < degree b) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ degree (A i₁ - A i₀) < ↑(natDegree b - d) := by
  have hb : b ≠ 0 := by
    rintro rfl
    specialize hA 0
    rw [degree_zero] at hA
    exact not_lt_of_le bot_le hA
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `degree b - 1`, ... `degree b - d`.
  -- In other words, the following map is not injective:
  set f : Fin m.succ → Fin d → Fq := fun i j => (A i).coeff (natDegree b - j.succ)
  have : Fintype.card (Fin d → Fq) < Fintype.card (Fin m.succ) := by
    simpa using lt_of_le_of_lt hm (Nat.lt_succ_self m)
  -- Therefore, the differences have all coefficients higher than `deg b - d` equal.
  obtain ⟨i₀, i₁, i_ne, i_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f this
  use i₀, i₁, i_ne
  refine (degree_lt_iff_coeff_zero _ _).mpr fun j hj => ?_
  -- The coefficients higher than `deg b` are the same because they are equal to 0.
  by_cases hbj : degree b ≤ j
  · refine coeff_eq_zero_of_degree_lt (lt_of_lt_of_le ?_ hbj)
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (hA _) (hA _))
  -- So we only need to look for the coefficients between `deg b - d` and `deg b`.
  rw [coeff_sub, sub_eq_zero]
  rw [not_le, degree_eq_natDegree hb] at hbj
  have hbj : j < natDegree b := (@WithBot.coe_lt_coe _ _ _).mp hbj
  have hj : natDegree b - j.succ < d := by
    by_cases hd : natDegree b < d
    · exact lt_of_le_of_lt tsub_le_self hd
    · rw [not_lt] at hd
      have := lt_of_le_of_lt hj (Nat.lt_succ_self j)
      rwa [tsub_lt_iff_tsub_lt hd hbj] at this
  have : j = b.natDegree - (natDegree b - j.succ).succ := by
    rw [← Nat.succ_sub hbj, Nat.succ_sub_succ, tsub_tsub_cancel_of_le hbj.le]
  convert congr_fun i_eq.symm ⟨natDegree b - j.succ, hj⟩

variable [Field Fq]

-- DISSOLVED: exists_approx_polynomial

theorem cardPowDegree_anti_archimedean {x y z : Fq[X]} {a : ℤ} (hxy : cardPowDegree (x - y) < a)
    (hyz : cardPowDegree (y - z) < a) : cardPowDegree (x - z) < a := by
  have ha : 0 < a := lt_of_le_of_lt (AbsoluteValue.nonneg _ _) hxy
  by_cases hxy' : x = y
  · rwa [hxy']
  by_cases hyz' : y = z
  · rwa [← hyz']
  by_cases hxz' : x = z
  · rwa [hxz', sub_self, map_zero]
  rw [← Ne, ← sub_ne_zero] at hxy' hyz' hxz'
  refine lt_of_le_of_lt ?_ (max_lt hxy hyz)
  rw [cardPowDegree_nonzero _ hxz', cardPowDegree_nonzero _ hxy',
    cardPowDegree_nonzero _ hyz']
  have : (1 : ℤ) ≤ Fintype.card Fq := mod_cast (@Fintype.one_lt_card Fq _ _).le
  simp only [Int.cast_pow, Int.cast_natCast, le_max_iff]
  refine Or.imp (pow_le_pow_right₀ this) (pow_le_pow_right₀ this) ?_
  rw [natDegree_le_iff_degree_le, natDegree_le_iff_degree_le, ← le_max_iff, ←
    degree_eq_natDegree hxy', ← degree_eq_natDegree hyz']
  convert degree_add_le (x - y) (y - z) using 2
  exact (sub_add_sub_cancel _ _ _).symm

-- DISSOLVED: exists_partition_polynomial_aux

-- DISSOLVED: exists_partition_polynomial

noncomputable def cardPowDegreeIsAdmissible :
    IsAdmissible (cardPowDegree : AbsoluteValue Fq[X] ℤ) :=
  { @cardPowDegree_isEuclidean Fq _
      _ with
    card := fun ε => Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊
    exists_partition' := fun n _ hε _ hb => exists_partition_polynomial n hε hb }

end Polynomial
