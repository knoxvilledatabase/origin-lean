/-
Extracted from Data/Fin/Tuple/NatAntidiagonal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Collections of tuples of naturals with the same sum

This file generalizes `List.Nat.Antidiagonal n`, `Multiset.Nat.Antidiagonal n`, and
`Finset.Nat.Antidiagonal n` from the pair of elements `x : ℕ × ℕ` such that `n = x.1 + x.2`, to
the sequence of elements `x : Fin k → ℕ` such that `n = ∑ i, x i`.

## Main definitions

* `List.Nat.antidiagonalTuple`
* `Multiset.Nat.antidiagonalTuple`
* `Finset.Nat.antidiagonalTuple`

## Main results

* `antidiagonalTuple 2 n` is analogous to `antidiagonal n`:

  * `List.Nat.antidiagonalTuple_two`
  * `Multiset.Nat.antidiagonalTuple_two`
  * `Finset.Nat.antidiagonalTuple_two`

## Implementation notes

While we could implement this by filtering `(Fintype.PiFinset fun _ ↦ range (n + 1))` or similar,
this implementation would be much slower.

In the future, we could consider generalizing `Finset.Nat.antidiagonalTuple` further to
support finitely-supported functions, as in `Finset.finsuppAntidiag` from
`Mathlib/Algebra/Order/Antidiag/Finsupp.lean`.
-/

/-! ### Lists -/

namespace List.Nat

def antidiagonalTuple : ∀ k, ℕ → List (Fin k → ℕ)
  | 0, 0 => [![]]
  | 0, _ + 1 => []
  | k + 1, n =>
    (List.Nat.antidiagonal n).flatMap fun ni =>
      (antidiagonalTuple k ni.2).map fun x => Fin.cons ni.1 x
