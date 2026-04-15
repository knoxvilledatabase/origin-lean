/-
Extracted from RingTheory/Henselian.lean
Genuine: 2 of 7 | Dissolved: 1 | Infrastructure: 4
-/
import Origin.Core

/-!
# Henselian rings

In this file we set up the basic theory of Henselian (local) rings.
A ring `R` is *Henselian* at an ideal `I` if the following conditions hold:
* `I` is contained in the Jacobson radical of `R`
* for every polynomial `f` over `R`, with a *simple* root `a₀` over the quotient ring `R/I`,
  there exists a lift `a : R` of `a₀` that is a root of `f`.

(Here, saying that a root `b` of a polynomial `g` is *simple* means that `g.derivative.eval b` is a
unit. Warning: if `R/I` is not a field then it is not enough to assume that `g` has a factorization
into monic linear factors in which `X - b` shows up only once; for example `1` is not a simple root
of `X^2-1` over `ℤ/4ℤ`.)

A local ring `R` is *Henselian* if it is Henselian at its maximal ideal.
In this case the first condition is automatic, and in the second condition we may ask for
`f.derivative.eval a ≠ 0`, since the quotient ring `R/I` is a field in this case.

## Main declarations

* `HenselianRing`: a typeclass on commutative rings,
  asserting that the ring is Henselian at the ideal `I`.
* `HenselianLocalRing`: a typeclass on commutative rings, asserting that the ring is local Henselian
* `Field.henselian`: fields are Henselian local rings
* `Henselian.TFAE`: equivalent ways of expressing the Henselian property for local rings
* `IsAdicComplete.henselianRing`:
  a ring `R` with ideal `I` that is `I`-adically complete is Henselian at `I`

## References

https://stacks.math.columbia.edu/tag/04GE

## TODO

After a good API for étale ring homomorphisms has been developed,
we can give more equivalent characterization of Henselian rings.

In particular, this can give a proof that factorizations into coprime polynomials can be lifted
from the residue field to the Henselian ring.

The following gist contains some code sketches in that direction.
https://gist.github.com/jcommelin/47d94e4af092641017a97f7f02bf9598

-/

noncomputable section

universe u v

open Polynomial IsLocalRing Function List

open scoped Ring

class HenselianRing (R : Type*) [CommRing R] (I : Ideal R) : Prop where
  jac : I ≤ Ideal.jacobson ⊥
  is_henselian :
    ∀ (f : R[X]) (_ : f.Monic) (a₀ : R) (_ : f.eval a₀ ∈ I)
      (_ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))), ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I

class HenselianLocalRing (R : Type*) [CommRing R] : Prop extends IsLocalRing R where
  is_henselian :
    ∀ (f : R[X]) (_ : f.Monic) (a₀ : R) (_ : f.eval a₀ ∈ maximalIdeal R)
      (_ : IsUnit (f.derivative.eval a₀)), ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R

-- INSTANCE (free from Core): (priority

-- DISSOLVED: HenselianLocalRing.TFAE

-- INSTANCE (free from Core): (R

-- INSTANCE (free from Core): (priority

open Polynomial in
