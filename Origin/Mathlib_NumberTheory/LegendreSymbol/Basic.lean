/-
Extracted from NumberTheory/LegendreSymbol/Basic.lean
Genuine: 17 | Conflates: 0 | Dissolved: 12 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

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

@[simp]
theorem at_zero : legendreSym p 0 = 0 := by rw [legendreSym, Int.cast_zero, MulChar.map_zero]

@[simp]
theorem at_one : legendreSym p 1 = 1 := by rw [legendreSym, Int.cast_one, MulChar.map_one]

protected theorem mul (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul, quadraticCharFun_mul]

@[simps]
def hom : ℤ →*₀ ℤ where
  toFun := legendreSym p
  map_zero' := at_zero p
  map_one' := at_one p
  map_mul' := legendreSym.mul p

-- DISSOLVED: sq_one

-- DISSOLVED: sq_one'

protected theorem mod (a : ℤ) : legendreSym p a = legendreSym p (a % p) := by
  simp only [legendreSym, intCast_mod]

-- DISSOLVED: eq_one_iff

-- DISSOLVED: eq_one_iff'

theorem eq_neg_one_iff {a : ℤ} : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p) :=
  quadraticChar_neg_one_iff_not_isSquare

theorem eq_neg_one_iff' {a : ℕ} : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p) := by
  rw [eq_neg_one_iff]; norm_cast

theorem card_sqrts (hp : p ≠ 2) (a : ℤ) :
    ↑{x : ZMod p | x ^ 2 = a}.toFinset.card = legendreSym p a + 1 :=
  quadraticChar_card_sqrts ((ringChar_zmod_n p).substr hp) a

end legendreSym

end Legendre

section QuadraticForm

/-!
### Applications to binary quadratic forms
-/

namespace legendreSym

-- DISSOLVED: eq_one_of_sq_sub_mul_sq_eq_zero

-- DISSOLVED: eq_one_of_sq_sub_mul_sq_eq_zero'

theorem eq_zero_mod_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : legendreSym p a = -1)
    {x y : ZMod p} (hxy : x ^ 2 - a * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have ha : (a : ZMod p) ≠ 0 := by
    intro hf
    rw [(eq_zero_iff p a).mpr hf] at h
    simp at h
  by_contra hf
  cases' imp_iff_or_not.mp (not_and'.mp hf) with hx hy
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero' ha hx hxy, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h

theorem prime_dvd_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : legendreSym p a = -1) {x y : ℤ}
    (hxy : (p : ℤ) ∣ x ^ 2 - a * y ^ 2) : ↑p ∣ x ∧ ↑p ∣ y := by
  simp_rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hxy ⊢
  push_cast at hxy
  exact eq_zero_mod_of_eq_neg_one h hxy

end legendreSym

end QuadraticForm

section Values

/-!
### The value of the Legendre symbol at `-1`

See `jacobiSym.at_neg_one` for the corresponding statement for the Jacobi symbol.
-/

variable {p : ℕ} [Fact p.Prime]

open ZMod

theorem legendreSym.at_neg_one (hp : p ≠ 2) : legendreSym p (-1) = χ₄ p := by
  simp only [legendreSym, card p, quadraticChar_neg_one ((ringChar_zmod_n p).substr hp),
    Int.cast_neg, Int.cast_one]

namespace ZMod

theorem exists_sq_eq_neg_one_iff : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 := by
  rw [FiniteField.isSquare_neg_one_iff, card p]

theorem mod_four_ne_three_of_sq_eq_neg_one {y : ZMod p} (hy : y ^ 2 = -1) : p % 4 ≠ 3 :=
  exists_sq_eq_neg_one_iff.1 ⟨y, hy ▸ pow_two y⟩

-- DISSOLVED: mod_four_ne_three_of_sq_eq_neg_sq'

-- DISSOLVED: mod_four_ne_three_of_sq_eq_neg_sq

end ZMod

end Values
