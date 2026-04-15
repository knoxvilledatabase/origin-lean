/-
Extracted from Data/Multiset/NatAntidiagonal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Antidiagonals in ℕ × ℕ as multisets

This file defines the antidiagonals of ℕ × ℕ as multisets: the `n`-th antidiagonal is the multiset
of pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines file `Data.List.NatAntidiagonal` and is further refined by file
`Data.Finset.NatAntidiagonal`.
-/

assert_not_exists Monoid

namespace Multiset

namespace Nat

def antidiagonal (n : ℕ) : Multiset (ℕ × ℕ) :=
  List.Nat.antidiagonal n
