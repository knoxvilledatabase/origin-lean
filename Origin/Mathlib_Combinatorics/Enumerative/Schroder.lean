/-
Extracted from Combinatorics/Enumerative/Schroder.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Schröder numbers

The Schröder numbers (https://oeis.org/A006318) are a sequence of integers that appear in various
combinatorial contexts.

## Main definitions

* `largeSchroder n`: the `n`th large Schröder number, defined recursively as `L 0 = 1` and
  `L (n + 1) = L n + ∑ i ≤ n, L i * L (n - i)`.
* `smallSchroder n`: the `n`th small Schröder number, defined as `S 0 = 1` and `S n = L n / 2`
  for `n > 0`.

## Main results

* `largeSchroder_even` : The large Schröder numbers are positive and even for `n > 0`.
* `smallSchroder_succ` : A recursive formula for small Schröder numbers:
  `S (n + 1) = 3 * S n + 2 * ∑ i < n - 2, S (i + 2) * S (n - 1 - i)`.

## Tags

Schroeder, Schroder
-/

open Finset

namespace Nat

variable {n : ℕ}

def largeSchroder : ℕ → ℕ
  | 0 => 1
  | n + 1 => largeSchroder n + ∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i)
