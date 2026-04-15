/-
Extracted from NumberTheory/ArithmeticFunction/Carmichael.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Carmichael function

## Main definitions

* `ArithmeticFunction.Carmichael`: the Carmichael function `λ`,
  also known as the reduced totient function.

## Main results

* A formula for `λ n` in terms of the prime factorization of `n`, given by the following theorems:
  `carmichael_two_pow_of_le_two`, `carmichael_two_pow_of_ne_two`, `carmichael_pow_of_prime_ne_two`,
  and `carmichael_factorization`.

## Notation

We use the standard notation `λ` to represent the Carmichael function,
which is accessible in the scope `ArithmeticFunction.Carmichael`.
Since the notation conflicts with the anonymous function notation, it is impossible to use this
notation in statements, but the pretty-printer will use it when showing the goal state.

## Tags

arithmetic functions, totient
-/

open Nat Monoid

variable {R : Type*}

namespace ArithmeticFunction

def Carmichael : ArithmeticFunction ℕ where
  toFun
    | 0 => 0
    | n + 1 => Nat.find <| ExponentExists.of_finite (G := (ZMod (n + 1))ˣ)
  map_zero' := rfl
