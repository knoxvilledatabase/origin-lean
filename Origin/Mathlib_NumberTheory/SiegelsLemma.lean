/-
Extracted from NumberTheory/SiegelsLemma.lean
Genuine: 4 of 8 | Dissolved: 3 | Infrastructure: 1
-/
import Origin.Core

/-!
# Siegel's Lemma

In this file we introduce and prove Siegel's Lemma in its most basic version. This is a fundamental
tool in diophantine approximation and transcendence and says that there exists a "small" integral
non-zero solution of a non-trivial underdetermined system of linear equations with integer
coefficients.

## Main results

- `exists_ne_zero_int_vec_norm_le`: Given a non-zero `m × n` matrix `A` with `m < n` the linear
  system it determines has a non-zero integer solution `t` with
  `‖t‖ ≤ ((n * ‖A‖) ^ ((m : ℝ) / (n - m)))`

## Notation

- `‖_‖ ` : Matrix.seminormedAddCommGroup is the sup norm, the maximum of the absolute values of
  the entries of the matrix

## References

See [M. Hindry and J. Silverman, Diophantine Geometry: an Introduction][hindrysilverman00].
-/

attribute [local instance] Matrix.seminormedAddCommGroup

open Matrix Finset

namespace Int.Matrix

variable {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)

local notation3 "m" => Fintype.card α

local notation3 "n" => Fintype.card β

local notation3 "e" => m / ((n : ℝ) - m) -- exponent

local notation3 "B" => Nat.floor (((n : ℝ) * max 1 ‖A‖) ^ e)

local notation3 "B'" => fun _ : β => (B : ℤ)

local notation3 "T" => Finset.Icc 0 B'

local notation3 "P" => fun i : α => ∑ j : β, B * posPart (A i j)

local notation3 "N" => fun i : α => ∑ j : β, B * (-negPart (A i j))

local notation3 "S" => Finset.Icc N P

section preparation

private lemma card_T_eq [DecidableEq β] : #T = (B + 1) ^ n := by
  rw [Pi.card_Icc 0 B']
  simp only [Pi.zero_apply, card_Icc, sub_zero, toNat_natCast_add_one, prod_const, card_univ]

private lemma N_le_P_add_one (i : α) : N i ≤ P i + 1 := by
  calc N i
  _ ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    simp only [mul_neg, Left.neg_nonpos_iff]
    positivity
  _ ≤ P i + 1 := by
    apply le_trans (Finset.sum_nonneg _) (Int.le_add_one (le_refl P i))
    intro j _
    positivity

private lemma card_S_eq [DecidableEq α] : #(Finset.Icc N P) = ∏ i : α, (P i - N i + 1) := by
  rw [Pi.card_Icc N P, Nat.cast_prod]
  congr
  ext i
  rw [Int.card_Icc_of_le (N i) (P i) (N_le_P_add_one A i)]
  exact add_sub_right_comm (P i) 1 (N i)

-- DISSOLVED: one_le_norm_A_of_ne_zero

open Real Nat

private lemma card_S_lt_card_T [DecidableEq α] [DecidableEq β]
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) :
    #S < #T := by
  zify -- This is necessary to use card_S_eq
  rw [card_T_eq A, card_S_eq]
  rify -- This is necessary because ‖A‖ is a real number
  calc
  ∏ x : α, (∑ x_1 : β, ↑B * ↑(A x x_1)⁺ - ∑ x_1 : β, ↑B * -↑(A x x_1)⁻ + 1)
    ≤ ∏ x : α, (n * max 1 ‖A‖ * B + 1) := by
      refine Finset.prod_le_prod (fun i _ ↦ ?_) (fun i _ ↦ ?_)
      · have h := N_le_P_add_one A i
        rify at h
        linarith only [h]
      · simp only [mul_neg, sum_neg_distrib, sub_neg_eq_add, add_le_add_iff_right]
        have h1 : n * max 1 ‖A‖ * B = ∑ _ : β, max 1 ‖A‖ * B := by
          simp
          ring
        simp_rw [h1, ← Finset.sum_add_distrib, ← mul_add, mul_comm (max 1 ‖A‖), ← Int.cast_add]
        gcongr with j _
        rw [posPart_add_negPart (A i j), Int.cast_abs]
        exact le_trans (norm_entry_le_entrywise_sup_norm A) (le_max_right ..)
  _ = (n * max 1 ‖A‖ * B + 1) ^ m := by simp
  _ ≤ (n * max 1 ‖A‖) ^ m * (B + 1) ^ m := by
        rw [← mul_pow, mul_add, mul_one]
        gcongr
        have H : 1 ≤ (n : ℝ) := mod_cast (hm.trans hn)
        exact one_le_mul_of_one_le_of_one_le H <| le_max_left ..
  _ = ((n * max 1 ‖A‖) ^ (m / ((n : ℝ) - m))) ^ ((n : ℝ) - m) * (B + 1) ^ m := by
        congr 1
        rw [← rpow_mul (mul_nonneg (Nat.cast_nonneg' n) (le_trans zero_le_one (le_max_left ..))),
          ← Real.rpow_natCast, div_mul_cancel₀]
        exact sub_ne_zero_of_ne (mod_cast hn.ne')
  _ < (B + 1) ^ ((n : ℝ) - m) * (B + 1) ^ m := by
        gcongr
        · exact sub_pos.mpr (mod_cast hn)
        · exact Nat.lt_floor_add_one ((n * max 1 ‖A‖) ^ e)
  _ = (B + 1) ^ n := by
        rw [← rpow_natCast, ← rpow_add (Nat.cast_add_one_pos B), ← rpow_natCast, sub_add_cancel]

end preparation

-- DISSOLVED: exists_ne_zero_int_vec_norm_le

-- DISSOLVED: exists_ne_zero_int_vec_norm_le'

end Int.Matrix
