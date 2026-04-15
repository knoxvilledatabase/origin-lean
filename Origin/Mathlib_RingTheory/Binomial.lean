/-
Extracted from RingTheory/Binomial.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Binomial rings

In this file we introduce the binomial property as a mixin, and define the `multichoose`
and `choose` functions generalizing binomial coefficients.

According to our main reference [elliott2006binomial] (which lists many equivalent conditions), a
binomial ring is a torsion-free commutative ring `R` such that for any `x ∈ R` and any `k ∈ ℕ`, the
product `x(x-1)⋯(x-k+1)` is divisible by `k!`. The torsion-free condition lets us divide by `k!`
unambiguously, so we get uniquely defined binomial coefficients.

The defining condition doesn't require commutativity or associativity, and we get a theory with
essentially the same power by replacing subtraction with addition. Thus, we consider any additive
commutative monoid with a notion of natural number exponents in which multiplication by positive
integers is injective, and demand that the evaluation of the ascending Pochhammer polynomial
`X(X+1)⋯(X+(k-1))` at any element is divisible by `k!`. The quotient is called `multichoose r k`,
because for `r` a natural number, it is the number of multisets of cardinality `k` taken from a type
of cardinality `n`.

## Definitions

* `BinomialRing`: a mixin class specifying a suitable `multichoose` function.
* `Ring.multichoose`: the quotient of an ascending Pochhammer evaluation by a factorial.
* `Ring.choose`: the quotient of a descending Pochhammer evaluation by a factorial.

## Results

* Basic results with choose and multichoose, e.g., `choose_zero_right`
* Relations between choose and multichoose, negated input.
* Fundamental recursion: `choose_succ_succ`
* Chu-Vandermonde identity: `add_choose_eq`
* Pochhammer API

## References

* [J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*][elliott2006binomial]

## TODO

Further results in Elliot's paper:
* A CommRing is binomial if and only if it admits a λ-ring structure with trivial Adams operations.
* The free commutative binomial ring on a set `X` is the ring of integer-valued polynomials in the
  variables `X`.  (also, noncommutative version?)
* Given a commutative binomial ring `A` and an `A`-algebra `B` that is complete with respect to an
  ideal `I`, formal exponentiation induces an `A`-module structure on the multiplicative subgroup
  `1 + I`.

-/

open Function Polynomial

class BinomialRing (R : Type*) [AddCommMonoid R] [Pow R ℕ] where
  -- This base class has been demoted to a field, to avoid creating
  -- an expensive global instance.
  [toIsAddTorsionFree : IsAddTorsionFree R]
  /-- A multichoose function, giving the quotient of Pochhammer evaluations by factorials. -/
  multichoose : R → ℕ → R
  /-- The `n`th ascending Pochhammer polynomial evaluated at any element is divisible by `n!` -/
  factorial_nsmul_multichoose (r : R) (n : ℕ) :
    n.factorial • multichoose r n = (ascPochhammer ℕ n).smeval r

attribute [local instance] BinomialRing.toIsAddTorsionFree

section Multichoose

namespace Ring

variable {R : Type*} [AddCommMonoid R] [Pow R ℕ] [BinomialRing R]

def multichoose (r : R) (n : ℕ) : R := BinomialRing.multichoose r n
