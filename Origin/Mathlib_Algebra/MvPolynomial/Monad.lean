/-
Extracted from Algebra/MvPolynomial/Monad.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Monad operations on `MvPolynomial`

This file defines two monadic operations on `MvPolynomial`. Given `p : MvPolynomial σ R`,

* `MvPolynomial.bind₁` and `MvPolynomial.join₁` operate on the variable type `σ`.
* `MvPolynomial.bind₂` and `MvPolynomial.join₂` operate on the coefficient type `R`.

- `MvPolynomial.bind₁ f φ` with `f : σ → MvPolynomial τ R` and `φ : MvPolynomial σ R`,
  is the polynomial `φ(f 1, ..., f i, ...) : MvPolynomial τ R`.
- `MvPolynomial.join₁ φ` with `φ : MvPolynomial (MvPolynomial σ R) R` collapses `φ` to
  a `MvPolynomial σ R`, by evaluating `φ` under the map `X f ↦ f` for `f : MvPolynomial σ R`.
  In other words, if you have a polynomial `φ` in a set of variables indexed by a polynomial ring,
  you evaluate the polynomial in these indexing polynomials.
- `MvPolynomial.bind₂ f φ` with `f : R →+* MvPolynomial σ S` and `φ : MvPolynomial σ R`
  is the `MvPolynomial σ S` obtained from `φ` by mapping the coefficients of `φ` through `f`
  and considering the resulting polynomial as polynomial expression in `MvPolynomial σ R`.
- `MvPolynomial.join₂ φ` with `φ : MvPolynomial σ (MvPolynomial σ R)` collapses `φ` to
  a `MvPolynomial σ R`, by considering `φ` as polynomial expression in `MvPolynomial σ R`.

These operations themselves have algebraic structure: `MvPolynomial.bind₁`
and `MvPolynomial.join₁` are algebra homs and
`MvPolynomial.bind₂` and `MvPolynomial.join₂` are ring homs.

They interact in convenient ways with `MvPolynomial.rename`, `MvPolynomial.map`,
`MvPolynomial.vars`, and other polynomial operations.
Indeed, `MvPolynomial.rename` is the "map" operation for the (`bind₁`, `join₁`) pair,
whereas `MvPolynomial.map` is the "map" operation for the other pair.

## Implementation notes

We add a `LawfulMonad` instance for the (`bind₁`, `join₁`) pair.
The second pair cannot be instantiated as a `Monad`,
since it is not a monad in `Type` but in `CommRingCat` (or rather `CommSemiRingCat`).

-/

noncomputable section

namespace MvPolynomial

open Finsupp

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

def bind₁ (f : σ → MvPolynomial τ R) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval f

def bind₂ (f : R →+* MvPolynomial σ S) : MvPolynomial σ R →+* MvPolynomial σ S :=
  eval₂Hom f X

def join₁ : MvPolynomial (MvPolynomial σ R) R →ₐ[R] MvPolynomial σ R :=
  aeval id

def join₂ : MvPolynomial σ (MvPolynomial σ R) →+* MvPolynomial σ R :=
  eval₂Hom (RingHom.id _) X
