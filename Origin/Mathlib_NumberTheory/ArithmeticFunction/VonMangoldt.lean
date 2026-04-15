/-
Extracted from NumberTheory/ArithmeticFunction/VonMangoldt.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The von Mangoldt Function

In this file we define the von Mangoldt function: the function on natural numbers that returns
`log p` if the input can be expressed as `p^k` for a prime `p`.

## Main Results

The main definition for this file is

- `ArithmeticFunction.vonMangoldt`: The von Mangoldt function `Λ`.

We then prove the classical summation property of the von Mangoldt function in
`ArithmeticFunction.vonMangoldt_sum`, that `∑ i ∈ n.divisors, Λ i = Real.log n`, and use this
to deduce alternative expressions for the von Mangoldt function via Möbius inversion, see
`ArithmeticFunction.sum_moebius_mul_log_eq`.

## Notation

We use the standard notation `Λ` to represent the von Mangoldt function.
It is accessible in the locales `ArithmeticFunction` (like the notations for other arithmetic
functions) and also in the scope `ArithmeticFunction.vonMangoldt`.

-/

namespace ArithmeticFunction

open Finset Nat

open scoped ArithmeticFunction

noncomputable def log : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n, by simp⟩
