/-
Extracted from Data/Rat/Cast/Lemmas.lean
Genuine: 6 | Conflates: 0 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Positivity.Basic

/-!
# Some exiled lemmas about casting

These lemmas have been removed from `Mathlib.Data.Rat.Cast.Defs`
to avoiding needing to import `Mathlib.Algebra.Field.Basic` there.

In fact, these lemmas don't appear to be used anywhere in Mathlib,
so perhaps this file can simply be deleted.
-/

namespace Rat

variable {α : Type*} [DivisionRing α]

@[simp, norm_cast]
lemma cast_pow (p : ℚ) (n : ℕ) : ↑(p ^ n) = (p ^ n : α) := by
  rw [cast_def, cast_def, den_pow, num_pow, Nat.cast_pow, Int.cast_pow, div_eq_mul_inv, ← inv_pow,
    ← (Int.cast_commute _ _).mul_pow, ← div_eq_mul_inv]

@[simp]
theorem cast_inv_nat (n : ℕ) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  cases' n with n
  · simp
  rw [cast_def, inv_natCast_num, inv_natCast_den, if_neg n.succ_ne_zero,
    Int.sign_eq_one_of_pos (Int.ofNat_succ_pos n), Int.cast_one, one_div]

@[simp]
theorem cast_inv_int (n : ℤ) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  cases' n with n n
  · simp [ofInt_eq_cast, cast_inv_nat]
  · simp only [ofInt_eq_cast, Int.cast_negSucc, ← Nat.cast_succ, cast_neg, inv_neg, cast_inv_nat]

@[simp, norm_cast]
theorem cast_nnratCast {K} [DivisionRing K] (q : ℚ≥0) :
    ((q : ℚ) : K) = (q : K) := by
  rw [Rat.cast_def, NNRat.cast_def, NNRat.cast_def]
  have hn := @num_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  on_goal 1 => have hd := @den_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  case hdp => simpa only [Int.ofNat_pos] using q.den_pos
  simp only [Int.cast_natCast, Nat.cast_inj] at hn hd
  rw [hn, hd, Int.cast_natCast]

@[simp, norm_cast]
theorem cast_ofScientific {K} [DivisionRing K] (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℚ) = (OfScientific.ofScientific m s e : K) := by
  rw [← NNRat.cast_ofScientific (K := K), ← NNRat.cast_ofScientific, cast_nnratCast]

end Rat

namespace NNRat

@[simp, norm_cast]
theorem cast_pow {K} [DivisionSemiring K] (q : ℚ≥0) (n : ℕ) :
    NNRat.cast (q ^ n) = (NNRat.cast q : K) ^ n := by
  rw [cast_def, cast_def, den_pow, num_pow, Nat.cast_pow, Nat.cast_pow, div_eq_mul_inv, ← inv_pow,
    ← (Nat.cast_commute _ _).mul_pow, ← div_eq_mul_inv]

-- DISSOLVED: cast_zpow_of_ne_zero

open OfScientific in

theorem Nonneg.coe_ofScientific {K} [LinearOrderedField K] (m : ℕ) (s : Bool) (e : ℕ) :
    (ofScientific m s e : {x : K // 0 ≤ x}).val = ofScientific m s e := rfl

end NNRat
