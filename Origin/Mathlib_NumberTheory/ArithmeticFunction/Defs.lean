/-
Extracted from NumberTheory/ArithmeticFunction/Defs.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Arithmetic Functions and Dirichlet Convolution

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions

* `ArithmeticFunction R` consists of functions `f : ℕ → R` such that `f 0 = 0`.
* An arithmetic function `f` `IsMultiplicative` when `x.Coprime y → f (x * y) = f x * f y`.
* Multiplication and power instances on `ArithmeticFunction R`, are defined using Dirichlet
  convolution.

Further examples of arithmetic functions, such as the Möbius function `μ`, are available in
other files in the `Mathlib.NumberTheory.ArithmeticFunction` directory.

## Tags

arithmetic functions, dirichlet convolution, divisors
-/

open Finset

open Nat

variable (R : Type*)

def ArithmeticFunction [Zero R] :=
  ZeroHom ℕ R

-- INSTANCE (free from Core): ArithmeticFunction.zero

-- INSTANCE (free from Core): [Zero

variable {R}

namespace ArithmeticFunction

section Zero

variable [Zero R]

-- INSTANCE (free from Core): :
