/-
Extracted from NumberTheory/PrimeCounting.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Prime Counting Function

In this file we define the prime counting function: the function on natural numbers that returns
the number of primes less than or equal to its input.

## Main Results

The main definitions for this file are

- `Nat.primeCounting`: The prime counting function π
- `Nat.primeCounting'`: π(n - 1)

We then prove that these are monotone in `Nat.monotone_primeCounting` and
`Nat.monotone_primeCounting'`. The last main theorem `Nat.primeCounting'_add_le` is an upper
bound on `π'` which arises by observing that all numbers greater than `k` and not coprime to `k`
are not prime, and so only at most `φ(k)/k` fraction of the numbers from `k` to `n` are prime.

## Notation

With `open scoped Nat.Prime`, we use the standard notation `π` to represent the prime counting
function (and `π'` to represent the reindexed version).

-/

namespace Nat

open Finset

def primeCounting' : ℕ → ℕ :=
  Nat.count Prime

def primeCounting (n : ℕ) : ℕ :=
  primeCounting' (n + 1)
