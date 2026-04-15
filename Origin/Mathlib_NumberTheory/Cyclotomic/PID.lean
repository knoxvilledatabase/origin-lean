/-
Extracted from NumberTheory/Cyclotomic/PID.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.Cyclotomic.Embeddings

/-!
# Cyclotomic fields whose ring of integers is a PID.
We prove that `ℤ [ζₚ]` is a PID for specific values of `p`. The result holds for `p ≤ 19`,
but the proof is more and more involved.

## Main results
* `three_pid`: If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain.
* `five_pid`: If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain.
-/

universe u

namespace IsCyclotomicExtension.Rat

open NumberField Polynomial InfinitePlace Nat Real cyclotomic

variable (K : Type u) [Field K] [NumberField K]

theorem three_pid [IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [absdiscr_prime 3 K, IsCyclotomicExtension.finrank (n := 3) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 3, totient_prime
      PNat.prime_three]
  simp only [Int.reduceNeg, PNat.val_ofNat, succ_sub_succ_eq_sub, tsub_zero, zero_lt_two,
    Nat.div_self, pow_one, cast_ofNat, neg_mul, one_mul, abs_neg, Int.cast_abs, Int.cast_ofNat,
    factorial_two, gt_iff_lt, abs_of_pos (show (0 : ℝ) < 3 by norm_num)]
  suffices (2 * (3 / 4) * (2 ^ 2 / 2)) ^ 2 < (2 * (π / 4) * (2 ^ 2 / 2)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

theorem five_pid [IsCyclotomicExtension {5} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [absdiscr_prime 5 K, IsCyclotomicExtension.finrank (n := 5) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 5, totient_prime
      PNat.prime_five]
  simp only [Int.reduceNeg, PNat.val_ofNat, succ_sub_succ_eq_sub, tsub_zero, reduceDiv, even_two,
    Even.neg_pow, one_pow, cast_ofNat, Int.reducePow, one_mul, Int.cast_abs, Int.cast_ofNat,
    div_pow, gt_iff_lt, show 4! = 24 by rfl, abs_of_pos (show (0 : ℝ) < 125 by norm_num)]
  suffices (2 * (3 ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 < (2 * (π ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

end IsCyclotomicExtension.Rat
