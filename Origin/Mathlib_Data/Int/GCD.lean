/-
Extracted from Data/Int/GCD.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extended GCD and divisibility over ℤ

## Main definitions

* Given `x y : ℕ`, `xgcd x y` computes the pair of integers `(a, b)` such that
  `gcd x y = x * a + y * b`. `gcdA x y` and `gcdB x y` are defined to be `a` and `b`,
  respectively.

## Main statements

* `gcd_eq_gcd_ab`: Bézout's lemma, given `x y : ℕ`, `gcd x y = x * gcdA x y + y * gcdB x y`.

## Tags

Bézout's lemma, Bezout's lemma
-/

/-! ### Extended Euclidean algorithm -/

namespace Nat

def xgcdAux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ :=
  Nat.strongRec' fun n ih s t r' s' t' ↦ match n with
  | 0 => (r', s', t')
  | succ k =>
    let q := r' / succ k
    ih (r' % succ k) (mod_lt _ <| (succ_pos _).gt) (s' - q * s) (t' - q * t) (succ k) s t
