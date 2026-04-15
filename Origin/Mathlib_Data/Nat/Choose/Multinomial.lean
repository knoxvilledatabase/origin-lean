/-
Extracted from Data/Nat/Choose/Multinomial.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Multinomial

This file defines the multinomial coefficients and several small lemmas for manipulating them.

- `Nat.multinomial`: the multinomial coefficient,
  Given a function `f : α → ℕ` and `s : Finset α`, this is the number of strings
  consisting of symbols from `s`, where `c ∈ s` appears with multiplicity `f c`.

  It is defined as `(∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!`.

- `Multiset.countPerms`: multinomial coefficient associated with the `Multiset.count` function
  of a multiset. This is the number of lists that induce the given multiset.

- `Finset.sum_pow`: The expansion of `(s.sum x) ^ n` using multinomial coefficients

- `Multiset.multinomial`.
  Given a multiset `m` of natural numbers, `m.multinomial` is the
  multinomial coefficient defined by `(m.sum) ! / ∏ i ∈ m, m i !`.

This should not be confused with `m.countPerms` which
is defined as `m.toFinsupp.multinomial`.

As an example, one has `Multiset.multinomial {1, 2, 2} = 30`,
while `Multiset.countPerms {1, 2, 2} = 3`.

- `Multiset.multinomial_cons` proves that
  `(x ::ₘ m).multinomial = Nat.choose (x + m.sum) x * m.multinomial`
- `Multiset.multinomial_add` proves that
  `(m + m').multinomial = Nat.choose (m + m').sum m.sum * m.multinomial * m'.multinomial`

## Implementation note for `Multiset.multinomial`.

To avoid the definition of `Multiset.multinomial` as a quotient given above,
we define it in terms of `Finsupp.multinomial`, via lists:
If `m : Multiset ℕ` is the multiset associated with a list `l : List ℕ`,
then `m.multinomial = l.toFinsupp.multinomial`.
Then we prove its invariance under permutation.

-/

open Finset

open scoped Nat

namespace Nat

variable {α : Type*} (s : Finset α) (f : α → ℕ) {a b : α} (n : ℕ)

def multinomial : ℕ :=
  (∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!

theorem multinomial_pos : 0 < multinomial s f :=
  Nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f))
    (prod_factorial_pos s f)

theorem multinomial_spec : (∏ i ∈ s, (f i)!) * multinomial s f = (∑ i ∈ s, f i)! :=
  Nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)
