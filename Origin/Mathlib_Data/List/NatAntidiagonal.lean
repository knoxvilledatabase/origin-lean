/-
Extracted from Data/List/NatAntidiagonal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Antidiagonals in ℕ × ℕ as lists

This file defines the antidiagonals of ℕ × ℕ as lists: the `n`-th antidiagonal is the list of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

Files `Data.Multiset.NatAntidiagonal` and `Data.Finset.NatAntidiagonal` successively turn the
`List` definition we have here into `Multiset` and `Finset`.
-/

open Function

namespace List

namespace Nat

def antidiagonal (n : ℕ) : List (ℕ × ℕ) :=
  (range (n + 1)).map fun i ↦ (i, n - i)
