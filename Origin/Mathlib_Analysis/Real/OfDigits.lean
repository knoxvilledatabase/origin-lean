/-
Extracted from Analysis/Real/OfDigits.lean
Genuine: 13 of 20 | Dissolved: 7 | Infrastructure: 0
-/
import Origin.Core

/-!
# Representation of reals in positional system

This file defines `Real.ofDigits` and `Real.digits` functions which allows to work with the
representations of reals as sequences of digits in positional system.

## Main Definitions

* `ofDigits`: takes a sequence of digits `(d₀, d₁, ...)` (as an `ℕ → Fin b`),
  and returns the real number `0.d₀d₁d₂...`.
* `digits`: takes a real number in $[0,1)$ and returns the sequence of its digits.

## Main Statements

* `ofDigits_digits` states that `ofDigits (digits x b) = x`.
-/

namespace Real

noncomputable def ofDigitsTerm {b : ℕ} (digits : ℕ → Fin b) : ℕ → ℝ :=
  fun i ↦ (digits i) * ((b : ℝ) ^ (i + 1))⁻¹

theorem ofDigitsTerm_nonneg {b : ℕ} {digits : ℕ → Fin b} {n : ℕ} :
    0 ≤ ofDigitsTerm digits n := by
  simp only [ofDigitsTerm]
  positivity

private lemma b_pos {b : ℕ} (digits : ℕ → Fin b) : 0 < b := Fin.pos (digits 0)

theorem ofDigitsTerm_le {b : ℕ} {digits : ℕ → Fin b} {n : ℕ} :
    ofDigitsTerm digits n ≤ (b - 1) * ((b : ℝ) ^ (n + 1))⁻¹ := by
  obtain ⟨c, rfl⟩ := Nat.exists_add_one_eq.mpr (b_pos digits)
  unfold ofDigitsTerm
  gcongr
  simp
  grind

theorem summable_ofDigitsTerm {b : ℕ} {digits : ℕ → Fin b} :
    Summable (ofDigitsTerm digits) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ ofDigitsTerm_nonneg) (fun _ ↦ ofDigitsTerm_le) ?_
  obtain rfl | hb := (Nat.one_le_of_lt (b_pos digits)).eq_or_lt
  · simp
  simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
  refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
  simp [inv_lt_one_iff₀, hb]

noncomputable def ofDigits {b : ℕ} (digits : ℕ → Fin b) : ℝ :=
  ∑' n, ofDigitsTerm digits n

theorem ofDigits_nonneg {b : ℕ} (digits : ℕ → Fin b) : 0 ≤ ofDigits digits := by
  simp only [ofDigits]
  exact tsum_nonneg fun _ ↦ ofDigitsTerm_nonneg

theorem ofDigits_le_one {b : ℕ} (digits : ℕ → Fin b) : ofDigits digits ≤ 1 := by
  obtain rfl | hb := (Nat.one_le_of_lt (b_pos digits)).eq_or_lt
  · simp [ofDigits, ofDigitsTerm]
  rify at hb
  convert Summable.tsum_mono summable_ofDigitsTerm _ (fun _ ↦ ofDigitsTerm_le)
  · simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by simp [inv_lt_one_iff₀, hb])]
    have := sub_pos.mpr hb
    field
  · simp_rw [pow_succ', mul_inv, ← inv_pow, ← mul_assoc]
    refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
    simp [inv_lt_one_iff₀, hb]

theorem ofDigits_eq_sum_add_ofDigits {b : ℕ} (a : ℕ → Fin b) (n : ℕ) :
    ofDigits a = (∑ i ∈ Finset.range n, ofDigitsTerm a i) +
      ((b : ℝ) ^ n)⁻¹ * ofDigits (fun i ↦ a (i + n)) := by
  simp only [ofDigits]
  rw [← Summable.sum_add_tsum_nat_add n summable_ofDigitsTerm,
    ← Summable.tsum_mul_left _ summable_ofDigitsTerm]
  congr
  ext i
  simp only [ofDigitsTerm]
  ring

theorem abs_ofDigits_sub_ofDigits_le {b : ℕ} {x y : ℕ → Fin b} {n : ℕ}
    (hxy : ∀ i < n, x i = y i) :
    |ofDigits x - ofDigits y| ≤ ((b : ℝ) ^ n)⁻¹ := by
  rw [ofDigits_eq_sum_add_ofDigits x n, ofDigits_eq_sum_add_ofDigits y n]
  have : ∑ i ∈ Finset.range n, ofDigitsTerm x i = ∑ i ∈ Finset.range n, ofDigitsTerm y i :=
    Finset.sum_congr rfl fun i hi ↦ by simp [ofDigitsTerm, hxy i (Finset.mem_range.mp hi)]
  rw [this, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  apply mul_le_of_le_one_right (by positivity)
  convert abs_sub_le_of_le_of_le (ofDigits_nonneg _) (ofDigits_le_one _)
    (ofDigits_nonneg _) (ofDigits_le_one _)
  simp

-- DISSOLVED: digits

-- DISSOLVED: ofDigits_digits_sum_eq

-- DISSOLVED: le_sum_ofDigitsTerm_digits

-- DISSOLVED: sum_ofDigitsTerm_digits_le

-- DISSOLVED: hasSum_ofDigitsTerm_digits

-- DISSOLVED: ofDigits_digits

-- DISSOLVED: ofDigits_const_last_eq_one

theorem ofDigits_const_last_eq_one' {b : ℕ} (hb : 1 < b) :
    ofDigits (fun _ ↦ (⟨b - 1, Nat.sub_one_lt_of_lt hb⟩ : Fin b)) = 1 := by
  convert ofDigits_const_last_eq_one (b - 1)
  · grind
  · constructor
    grind

theorem ofDigits_SurjOn {b : ℕ} (hb : 1 < b) :
    Set.SurjOn (ofDigits (b := b)) Set.univ (Set.Icc 0 1) := by
  have : NeZero b := ⟨by grind⟩
  intro y hy
  by_cases hy' : y ∈ Set.Ico 0 1
  · use digits y b
    simp [ofDigits_digits hb hy']
  · simp only [Set.image_univ, show y = 1 by grind, Set.mem_range]
    exact ⟨_, ofDigits_const_last_eq_one' hb⟩

theorem continuous_ofDigits {b : ℕ} : Continuous (@ofDigits b) := by
  match b with
  | 0 => fun_prop
  | 1 => fun_prop
  | n + 2 =>
    obtain ⟨hb0, hb⟩ : 0 < n + 2 ∧ 1 < n + 2 := by grind
    generalize n + 2 = b at hb
    rify at hb0 hb
    refine continuous_tsum (u := fun i ↦ (b : ℝ)⁻¹ ^ i) ?_ ?_ fun n x ↦ ?_
    · simp only [ofDigitsTerm]
      fun_prop
    · exact summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb)
    · simp only [norm_eq_abs, abs_of_nonneg ofDigitsTerm_nonneg, inv_pow]
      apply ofDigitsTerm_le.trans
      calc
        _ ≤ b * ((b : ℝ) ^ (n + 1))⁻¹ := by
          gcongr
          linarith
        _ = _ := by
          grind

end Real
