/-
Extracted from Data/Nat/Choose/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Binomial coefficients

This file defines binomial coefficients and proves simple lemmas (i.e. those not
requiring more imports).
For the lemma that `n.choose k` counts the `k`-element-subsets of an `n`-element set,
see `Finset.card_powersetCard` in `Mathlib/Data/Finset/Powerset.lean`.

## Main definition and results

* `Nat.choose`: binomial coefficients, defined inductively
* `Nat.choose_eq_factorial_div_factorial`: a proof that `choose n k = n! / (k! * (n - k)!)`
* `Nat.choose_symm`: symmetry of binomial coefficients
* `Nat.choose_le_succ_of_lt_half_left`: `choose n k` is increasing for small values of `k`
* `Nat.choose_le_middle`: `choose n r` is maximised when `r` is `n/2`
* `Nat.descFactorial_eq_factorial_mul_choose`: Relates binomial coefficients to the descending
  factorial. This is used to prove `Nat.choose_le_pow` and variants. We provide similar statements
  for the ascending factorial.
* `Nat.multichoose`: whereas `choose` counts combinations, `multichoose` counts multicombinations.
  The fact that this is indeed the correct counting function for multisets is proved in
  `Sym.card_sym_eq_multichoose` in `Data.Sym.Card`.
* `Nat.multichoose_eq` : a proof that `multichoose n k = (n + k - 1).choose k`.
  This is central to the "stars and bars" technique in informal mathematics, where we switch between
  counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
  ("stars") separated by `n-1` dividers ("bars").  See `Data.Sym.Card` for more detail.

## Tags

binomial coefficient, combination, multicombination, stars and bars
-/

namespace Nat

def choose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)
