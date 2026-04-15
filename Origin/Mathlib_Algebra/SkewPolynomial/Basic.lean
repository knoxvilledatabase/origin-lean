/-
Extracted from Algebra/SkewPolynomial/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Univariate skew polynomials

Given a ring `R` and an endomorphism `φ` on `R` the skew polynomials over `R`
are polynomials
$$\sum_{i= 0}^n a_iX^n, n\geq 0, a_i\in R$$
where the addition is the usual addition of polynomials
$$\sum_{i= 0}^n a_iX^n + \sum_{i= 0}^n b_iX^n= \sum_{i= 0}^n (a_i + b_i)X^n.$$
The multiplication, however, is determined by
$$Xa = \varphi (a)X$$
by extending it to all polynomials in the obvious way.

Skew polynomials are represented as `SkewMonoidAlgebra R (Multiplicative ℕ)`,
where `R` is usually at least a Semiring. In this file, we define `SkewPolynomial`
and provide basic instances.

**Note**: To register the endomorphism `φ` see notation below.

## Notation

The endomorphism `φ` is implemented using some action of `Multiplicative ℕ` on `R`.
From this action, `φ` is an `abbrev` denoting $(\text{ofAdd } 1) \cdot a := \varphi(a)$.

Users that want to work with a specific map `φ` should introduce an an action of
`Multiplicative ℕ` on `R`. Specifying that this action is a `MulSemiringAction` amounts
to saying that `φ` is an endomorphism.

Furthermore, with this notation `φ^[n](a) = (ofAdd n) • a`, see `φ_iterate_apply`.

## Implementation notes

The implementation uses `Multiplicative ℕ` instead of `ℕ` as some notion
of `AddSkewMonoidAlgebra` like the current implementation of `Polynomials` in Mathlib.

This decision was made because we use the type class `MulSemiringAction` to specify the properties
the action needs to respect for associativity. There is no version of this in Mathlib that
uses an acting `AddMonoid M` and so we need to use `Multiplicative ℕ` for the action.

For associativity to hold, there should be an instance of
`MulSemiringAction (Multiplicative ℕ) R` present in the context.
For example, in the context of $\mathbb{F}_q$-linear polynomials, this can be the
$q$-th Frobenius endomorphism - so $\varphi(a) = a^q$.

## Reference

The definition is inspired by Chapter 3 of [Papikian2023].

## Tags

Skew Polynomials, Twisted Polynomials.

## TODO :
  - Add algebra instance
  - Add `ext` lemma in terms of `Coeff`.

Note that [ore33] proposes a more general definition of skew polynomial ring, where the
multiplication is determined by  $Xa = \varphi (a)X + δ (a)$, where `ϕ` is as above and
`δ` is a derivation.

-/

noncomputable section

open Multiplicative SkewMonoidAlgebra

abbrev SkewPolynomial (R : Type*) [AddCommMonoid R] := SkewMonoidAlgebra R (Multiplicative ℕ)

namespace SkewPolynomial

variable {R : Type*}

section Semiring

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

def support (p : SkewPolynomial R) : Finset ℕ :=
  Finset.map ⟨toAdd, toAdd.injective⟩ (SkewMonoidAlgebra.support p)
