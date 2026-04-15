/-
Extracted from Data/Nat/Factorial/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Factorial and variants

This file defines the factorial, along with the ascending and descending variants.
For the proof that the factorial of `n` counts the permutations of an `n`-element set,
see `Fintype.card_perm`.

## Main declarations

* `Nat.factorial`: The factorial.
* `Nat.ascFactorial`: The ascending factorial. It is the product of natural numbers from `n` to
  `n + k - 1`.
* `Nat.descFactorial`: The descending factorial. It is the product of natural numbers from
  `n - k + 1` to `n`.
-/

namespace Nat

def factorial : ℕ → ℕ
  | 0 => 1
  | succ n => succ n * factorial n

scoped notation:10000 n "!" => Nat.factorial n

section Factorial

variable {m n : ℕ}
