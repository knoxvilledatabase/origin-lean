/-
Extracted from Data/Nat/Factorization/Root.lean
Genuine: 14 | Conflates: 0 | Dissolved: 8 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Factorization.Defs

/-!
# Roots of natural numbers, rounded up and down

This file defines the flooring and ceiling root of a natural number.
`Nat.floorRoot n a`/`Nat.ceilRoot n a`, the `n`-th flooring/ceiling root of `a`, is the natural
number whose `p`-adic valuation is the floor/ceil of the `p`-adic valuation of `a`.

For example the `2`-nd flooring and ceiling roots of `2^3 * 3^2 * 5` are `2 * 3` and `2^2 * 3 * 5`
respectively. Note this is **not** the `n`-th root of `a` as a real number, rounded up or down.

These operations are respectively the right and left adjoints to the map `a ↦ a ^ n` where `ℕ` is
ordered by divisibility. This is useful because it lets us characterise the numbers `a` whose `n`-th
power divide `n` as the divisors of some fixed number (aka `floorRoot n b`). See
`Nat.pow_dvd_iff_dvd_floorRoot`. Similarly, it lets us characterise the `b` whose `n`-th power is a
multiple of `a` as the multiples of some fixed number (aka `ceilRoot n a`). See
`Nat.dvd_pow_iff_ceilRoot_dvd`.

## TODO

* `norm_num` extension
-/

open Finsupp

namespace Nat

variable {a b n : ℕ}

def floorRoot (n a : ℕ) : ℕ :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k ↦ p ^ (k / n)

lemma floorRoot_def :
    floorRoot n a = if n = 0 ∨ a = 0 then 0 else (a.factorization ⌊/⌋ n).prod (· ^ ·) := by
  unfold floorRoot; split_ifs with h <;> simp [Finsupp.floorDiv_def, prod_mapRange_index pow_zero]

@[simp] lemma floorRoot_zero_left (a : ℕ) : floorRoot 0 a = 0 := by simp [floorRoot]

@[simp] lemma floorRoot_zero_right (n : ℕ) : floorRoot n 0 = 0 := by simp [floorRoot]

@[simp] lemma floorRoot_one_left (a : ℕ) : floorRoot 1 a = a := by
  simp [floorRoot]; split_ifs <;> simp [*]

-- DISSOLVED: floorRoot_one_right

-- DISSOLVED: floorRoot_pow_self

-- DISSOLVED: floorRoot_ne_zero

@[simp] lemma floorRoot_eq_zero : floorRoot n a = 0 ↔ n = 0 ∨ a = 0 :=
  floorRoot_ne_zero.not_right.trans <| by simp only [not_and_or, ne_eq, not_not]

@[simp] lemma factorization_floorRoot (n a : ℕ) :
    (floorRoot n a).factorization = a.factorization ⌊/⌋ n := by
  rw [floorRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  refine prod_pow_factorization_eq_self fun p hp ↦ ?_
  have : p.Prime ∧ p ∣ a ∧ ¬a = 0 := by simpa using support_floorDiv_subset hp
  exact this.1

lemma pow_dvd_iff_dvd_floorRoot : a ^ n ∣ b ↔ a ∣ floorRoot n b := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  obtain rfl | ha := eq_or_ne a 0
  · simp [hn]
  rw [← factorization_le_iff_dvd (pow_ne_zero _ ha) hb,
    ← factorization_le_iff_dvd ha (floorRoot_ne_zero.2 ⟨hn, hb⟩), factorization_pow,
    factorization_floorRoot, le_floorDiv_iff_smul_le (β := ℕ →₀ ℕ) (pos_iff_ne_zero.2 hn)]

lemma floorRoot_pow_dvd : floorRoot n a ^ n ∣ a := pow_dvd_iff_dvd_floorRoot.2 dvd_rfl

def ceilRoot (n a : ℕ) : ℕ :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k ↦ p ^ ((k + n - 1) / n)

lemma ceilRoot_def :
    ceilRoot n a = if n = 0 ∨ a = 0 then 0 else (a.factorization ⌈/⌉ n).prod (· ^ ·) := by
  unfold ceilRoot
  split_ifs with h <;>
    simp [Finsupp.ceilDiv_def, prod_mapRange_index pow_zero, Nat.ceilDiv_eq_add_pred_div]

@[simp] lemma ceilRoot_zero_left (a : ℕ) : ceilRoot 0 a = 0 := by simp [ceilRoot]

@[simp] lemma ceilRoot_zero_right (n : ℕ) : ceilRoot n 0 = 0 := by simp [ceilRoot]

@[simp] lemma ceilRoot_one_left (a : ℕ) : ceilRoot 1 a = a := by
  simp [ceilRoot]; split_ifs <;> simp [*]

-- DISSOLVED: ceilRoot_one_right

-- DISSOLVED: ceilRoot_pow_self

-- DISSOLVED: ceilRoot_ne_zero

@[simp] lemma ceilRoot_eq_zero : ceilRoot n a = 0 ↔ n = 0 ∨ a = 0 :=
  ceilRoot_ne_zero.not_right.trans <| by simp only [not_and_or, ne_eq, not_not]

@[simp] lemma factorization_ceilRoot (n a : ℕ) :
    (ceilRoot n a).factorization = a.factorization ⌈/⌉ n := by
  rw [ceilRoot_def]
  split_ifs with h
  · obtain rfl | rfl := h <;> simp
  refine prod_pow_factorization_eq_self fun p hp ↦ ?_
  have : p.Prime ∧ p ∣ a ∧ ¬a = 0 := by simpa using support_ceilDiv_subset hp
  exact this.1

-- DISSOLVED: dvd_pow_iff_ceilRoot_dvd

-- DISSOLVED: dvd_ceilRoot_pow

end Nat
