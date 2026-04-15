/-
Extracted from NumberTheory/SmoothNumbers.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Smooth numbers

For `s : Finset ℕ` we define the set `Nat.factoredNumbers s` of "`s`-factored numbers"
consisting of the positive natural numbers all of whose prime factors are in `s`, and
we provide some API for this.

We then define the set `Nat.smoothNumbers n` consisting of the positive natural numbers all of
whose prime factors are strictly less than `n`. This is the special case `s = Finset.range n`
of the set of `s`-factored numbers.

We also define the finite set `Nat.primesBelow n` to be the set of prime numbers less than `n`.

The main definition `Nat.equivProdNatSmoothNumbers` establishes the bijection between
`ℕ × (smoothNumbers p)` and `smoothNumbers (p+1)` given by sending `(e, n)` to `p^e * n`.
Here `p` is a prime number. It is obtained from the more general bijection between
`ℕ × (factoredNumbers s)` and `factoredNumbers (s ∪ {p})`; see `Nat.equivProdNatFactoredNumbers`.

Additionally, we define `Nat.smoothNumbersUpTo N n` as the `Finset` of `n`-smooth numbers
up to and including `N`, and similarly `Nat.roughNumbersUpTo` for its complement in `{1, ..., N}`,
and we provide some API, in particular bounds for their cardinalities; see
`Nat.smoothNumbersUpTo_card_le` and `Nat.roughNumbersUpTo_card_le`.
-/

open scoped Finset

namespace Nat

def primesBelow (n : ℕ) : Finset ℕ := {p ∈ Finset.range n | p.Prime}
