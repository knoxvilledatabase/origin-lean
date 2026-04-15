/-
Extracted from NumberTheory/LegendreSymbol/Basic.lean
Genuine: 4 of 8 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core

/-!
# Legendre symbol

This file contains results about Legendre symbols.

We define the Legendre symbol $\Bigl(\frac{a}{p}\Bigr)$ as `legendreSym p a`.
Note the order of arguments! The advantage of this form is that then `legendreSym p`
is a multiplicative map.

The Legendre symbol is used to define the Jacobi symbol, `jacobiSym a b`, for integers `a`
and (odd) natural numbers `b`, which extends the Legendre symbol.

## Main results

We also prove the supplementary laws that give conditions for when `-1`
is a square modulo a prime `p`:
`legendreSym.at_neg_one` and `ZMod.exists_sq_eq_neg_one_iff` for `-1`.

See `NumberTheory.LegendreSymbol.QuadraticReciprocity` for the conditions when `2` and `-2`
are squares:
`legendreSym.at_two` and `ZMod.exists_sq_eq_two_iff` for `2`,
`legendreSym.at_neg_two` and `ZMod.exists_sq_eq_neg_two_iff` for `-2`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol
-/

open Nat

section Euler

namespace ZMod

variable (p : ℕ) [Fact p.Prime]

theorem euler_criterion_units (x : (ZMod p)ˣ) : (∃ y : (ZMod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 := by
  by_cases hc : p = 2
  · subst hc
    simp only [eq_iff_true_of_subsingleton, exists_const]
  · have h₀ := FiniteField.unit_isSquare_iff (by rwa [ringChar_zmod_n]) x
    have hs : (∃ y : (ZMod p)ˣ, y ^ 2 = x) ↔ IsSquare x := by
      rw [isSquare_iff_exists_sq x]
      simp_rw [eq_comm]
    rw [hs]
    rwa [card p] at h₀

-- DISSOLVED: euler_criterion

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: pow_div_two_eq_neg_one_or_one

end ZMod

end Euler

section Legendre

/-!
### Definition of the Legendre symbol and basic properties
-/

open ZMod

variable (p : ℕ) [Fact p.Prime]

def legendreSym (a : ℤ) : ℤ :=
  quadraticChar (ZMod p) a

namespace legendreSym

set_option backward.isDefEq.respectTransparency false in

theorem eq_pow (a : ℤ) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) := by
  rcases eq_or_ne (ringChar (ZMod p)) 2 with hc | hc
  · by_cases ha : (a : ZMod p) = 0
    · rw [legendreSym, ha, quadraticChar_zero,
        zero_pow (Nat.div_pos (@Fact.out p.Prime).two_le (succ_pos 1)).ne']
      norm_cast
    · have := (ringChar_zmod_n p).symm.trans hc
      -- p = 2
      subst p
      rw [legendreSym, quadraticChar_eq_one_of_char_two hc ha]
      revert ha
      push_cast
      generalize (a : ZMod 2) = b; fin_cases b
      · tauto
      · simp
  · convert quadraticChar_eq_pow_of_char_ne_two' hc (a : ZMod p)
    exact (card p).symm

-- DISSOLVED: eq_one_or_neg_one

-- DISSOLVED: eq_neg_one_iff_not_one

theorem eq_zero_iff (a : ℤ) : legendreSym p a = 0 ↔ (a : ZMod p) = 0 :=
  quadraticChar_eq_zero_iff
