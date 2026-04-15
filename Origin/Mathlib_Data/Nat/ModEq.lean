/-
Extracted from Data/Nat/ModEq.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Congruences modulo a natural number

This file defines the equivalence relation `a ≡ b [MOD n]` on the natural numbers,
and proves basic properties about it such as the Chinese Remainder Theorem
`modEq_and_modEq_iff_modEq_mul`.

## Notation

`a ≡ b [MOD n]` is notation for `Nat.ModEq n a b`, which is defined to mean `a % n = b % n`.

## Tags

ModEq, congruence, mod, MOD, modulo
-/

assert_not_exists IsOrderedMonoid Function.support

def Nat.ModEq (n a b : ℕ) :=
  a % n = b % n
