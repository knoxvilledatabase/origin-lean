/-
Extracted from NumberTheory/LSeries/Convolution.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dirichlet convolution of sequences and products of L-series

We define the *Dirichlet convolution* `f ⍟ g` of two sequences `f g : ℕ → R` with values in a
semiring `R` by `(f ⍟ g) n = ∑ (k * m = n), f k * g m` when `n ≠ 0` and `(f ⍟ g) 0 = 0`.
Technically, this is done by transporting the existing definition for `ArithmeticFunction R`;
see `LSeries.convolution`. We show that these definitions agree (`LSeries.convolution_def`).

We then consider the case `R = ℂ` and show that `L (f ⍟ g) = L f * L g` on the common domain
of convergence of the L-series `L f`  and `L g` of `f` and `g`; see `LSeries_convolution`
and `LSeries_convolution'`.
-/

open scoped LSeries.notation

open Complex LSeries

/-!
### Dirichlet convolution of two functions
-/

open Nat

def toArithmeticFunction {R : Type*} [Zero R] (f : ℕ → R) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else f n
  map_zero' := rfl

-- DISSOLVED: toArithmeticFunction_congr
