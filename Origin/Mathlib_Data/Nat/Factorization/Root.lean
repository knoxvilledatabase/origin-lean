/-
Extracted from Data/Nat/Factorization/Root.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

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
