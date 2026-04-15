/-
Extracted from Algebra/Group/NatPowAssoc.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Typeclasses for power-associative structures

In this file we define power-associativity for algebraic structures with a multiplication operation.
The class is a Prop-valued mixin named `NatPowAssoc`.

## Results

- `npow_add` a defining property: `x ^ (k + n) = x ^ k * x ^ n`
- `npow_one` a defining property: `x ^ 1 = x`
- `npow_assoc` strictly positive powers of an element have associative multiplication.
- `npow_comm` `x ^ m * x ^ n = x ^ n * x ^ m` for strictly positive `m` and `n`.
- `npow_mul` `x ^ (m * n) = (x ^ m) ^ n` for strictly positive `m` and `n`.
- `npow_eq_pow` monoid exponentiation coincides with semigroup exponentiation.

## Instances

We also produce the following instances:

- `NatPowAssoc` for Monoids, Pi types and products.

## TODO

* `to_additive`?

-/

assert_not_exists DenselyOrdered

variable {M : Type*}

class NatPowAssoc (M : Type*) [MulOneClass M] [Pow M ℕ] : Prop where
  /-- Multiplication is power-associative. -/
  protected npow_add : ∀ (k n : ℕ) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent zero is one. -/
  protected npow_zero : ∀ (x : M), x ^ 0 = 1
  /-- Exponent one is identity. -/
  protected npow_one : ∀ (x : M), x ^ 1 = x

section MulOneClass

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_add (k n : ℕ) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  NatPowAssoc.npow_add k n x
