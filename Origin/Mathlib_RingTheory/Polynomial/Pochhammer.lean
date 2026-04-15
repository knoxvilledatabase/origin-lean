/-
Extracted from RingTheory/Polynomial/Pochhammer.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Pochhammer polynomials

We define and prove some basic relations about
`ascPochhammer S n : S[X] := X * (X + 1) * ... * (X + n - 1)`
which is also known as the rising factorial and about
`descPochhammer R n : R[X] := X * (X - 1) * ... * (X - n + 1)`
which is also known as the falling factorial. Versions of this definition
that are focused on `Nat` can be found in `Data.Nat.Factorial` as `Nat.ascFactorial` and
`Nat.descFactorial`.

## Implementation

As with many other families of polynomials, even though the coefficients are always in `ℕ` or `ℤ`,
we define the polynomial with coefficients in any `[Semiring S]` or `[Ring R]`.
In an integral domain `S`, we show that `ascPochhammer S n` is zero iff
`n` is a sufficiently large non-positive integer.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
-/

universe u v

open Polynomial

section Semiring

variable (S : Type u) [Semiring S]

noncomputable def ascPochhammer : ℕ → S[X]
  | 0 => 1
  | n + 1 => X * (ascPochhammer n).comp (X + 1)
