/-
Extracted from Data/Nat/Factorial/SuperFactorial.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Superfactorial

This file defines the [superfactorial](https://en.wikipedia.org/wiki/Superfactorial)
`sf n = 1! * 2! * 3! * ... * n!`.

## Main declarations

* `Nat.superFactorial`: The superfactorial, denoted by `sf`.
-/

namespace Nat

def superFactorial : ℕ → ℕ
  | 0 => 1
  | succ n => factorial n.succ * superFactorial n

scoped notation "sf " n:60 => Nat.superFactorial n

section SuperFactorial
