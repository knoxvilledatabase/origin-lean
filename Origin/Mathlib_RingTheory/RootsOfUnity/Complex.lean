/-
Extracted from RingTheory/RootsOfUnity/Complex.lean
Genuine: 4 of 18 | Dissolved: 14 | Infrastructure: 0
-/
import Origin.Core

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `exp (2 * π * I * (i / n))` for `i ∈ Finset.range n`.

## Main declarations

* `Complex.mem_rootsOfUnity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `exp (2 * π * I * (i / n))` for some `i < n`.
* `Complex.card_rootsOfUnity`: the number of `n`-th roots of unity is exactly `n`.
* `Complex.norm_rootOfUnity_eq_one`: A complex root of unity has norm `1`.

-/

namespace Complex

open Polynomial Real

open scoped Nat Real

-- DISSOLVED: isPrimitiveRoot_exp_of_isCoprime

-- DISSOLVED: isPrimitiveRoot_exp_of_coprime

theorem isPrimitiveRoot_exp_rat (q : ℚ) : IsPrimitiveRoot (exp (2 * π * I * q)) q.den := by
  convert isPrimitiveRoot_exp_of_isCoprime _ _ q.den_nz <|
    Int.isCoprime_iff_nat_coprime.mpr q.reduced
  nth_rw 1 [← Rat.num_div_den q]
  simp

theorem isPrimitiveRoot_exp_rat_of_even_num (q : ℚ) (h : Even q.num) :
    IsPrimitiveRoot (exp (π * I * q)) q.den := by
  have ⟨n, hn⟩ := even_iff_exists_two_nsmul _ |>.mp h
  convert isPrimitiveRoot_exp_rat (n / q.den) using 1
  · nth_rw 1 [← q.num_div_den, hn, Int.nsmul_eq_mul]
    push_cast
    ring_nf
  · rw [← Int.cast_natCast, ← Rat.divInt_eq_div, ← Rat.mk_eq_divInt (nz := by simp)]
    apply Nat.Coprime.coprime_mul_left (k := 2)
    convert q.reduced
    grind

theorem isPrimitiveRoot_exp_rat_of_odd_num (q : ℚ) (h : Odd q.num) :
    IsPrimitiveRoot (exp (π * I * q)) (2 * q.den) := by
  convert isPrimitiveRoot_exp_rat (q / 2) using 1
  · push_cast
    ring_nf
  · nth_rw 2 [← q.num_div_den]
    rw [mul_comm, div_div, ← Int.cast_ofNat, ← Int.cast_natCast, ← Int.cast_mul,
      ← Rat.divInt_eq_div, ← Nat.cast_ofNat (R := ℤ), ← Nat.cast_mul,
      ← Rat.mk_eq_divInt (nz := by simp)
        (c := Nat.Coprime.mul_right q.reduced h.natAbs.coprime_two_right)]

-- DISSOLVED: isPrimitiveRoot_exp

-- DISSOLVED: isPrimitiveRoot_iff

-- DISSOLVED: mem_rootsOfUnity

-- DISSOLVED: card_rootsOfUnity

theorem card_primitiveRoots (k : ℕ) : (primitiveRoots k ℂ).card = φ k := by
  by_cases h : k = 0
  · simp [h]
  exact (isPrimitiveRoot_exp k h).card_primitiveRoots

end Complex

-- DISSOLVED: IsPrimitiveRoot.norm'_eq_one

-- DISSOLVED: IsPrimitiveRoot.nnnorm_eq_one

-- DISSOLVED: IsPrimitiveRoot.arg_ext

-- DISSOLVED: IsPrimitiveRoot.arg_eq_zero_iff

-- DISSOLVED: IsPrimitiveRoot.arg_eq_pi_iff

-- DISSOLVED: IsPrimitiveRoot.arg

-- DISSOLVED: Complex.norm_eq_one_of_mem_rootsOfUnity

-- DISSOLVED: Complex.conj_rootsOfUnity
