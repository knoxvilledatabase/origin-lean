/-
Extracted from Data/Int/ModEq.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Congruences modulo an integer

This file defines the equivalence relation `a ≡ b [ZMOD n]` on the integers, similarly to how
`Data.Nat.ModEq` defines them for the natural numbers. The notation is short for `n.ModEq a b`,
which is defined to be `a % n = b % n` for integers `a b n`.

## Tags

modeq, congruence, mod, MOD, modulo, integers

-/

def Int.ModEq (n a b : ℤ) :=
  a % n = b % n
