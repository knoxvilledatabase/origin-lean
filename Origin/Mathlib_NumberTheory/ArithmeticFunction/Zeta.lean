/-
Extracted from NumberTheory/ArithmeticFunction/Zeta.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The arithmetic function `ζ`

We define `ζ` to be the arithmetic function with `ζ n = 1` for `0 < n` (whose Dirichlet series
is the Riemann zeta function).

## Main Definitions

* `ArithmeticFunction.zeta` is the arithmetic function such that `ζ x = 1` for `0 < x`. The notation
  `ζ` for this function is available by opening `ArithmeticFunction.zeta`.
* `ArithmeticFunction.pmul` and `ArithmeticFunction.pdiv` are the pointwise multiplication and
  division on `ArithmeticFunction`s (for which `ζ` is the identity). These are not the same as
  the multiplication instance defined by Dirichlet convolution.

## Tags

arithmetic functions, dirichlet convolution, divisors
-/

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

def zeta : ArithmeticFunction ℕ :=
  ⟨fun x => ite (x = 0) 0 1, rfl⟩
