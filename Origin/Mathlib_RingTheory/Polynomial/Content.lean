/-
Extracted from RingTheory/Polynomial/Content.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# GCD structures on polynomials

Definitions and basic results about polynomials over GCD domains, particularly their contents
and primitive polynomials.

## Main Definitions
Let `p : R[X]`.
- `p.content` is the `gcd` of the coefficients of `p`.
- `p.IsPrimitive` indicates that `p.content = 1`.

## Main Results
- `Polynomial.content_mul`: if `p q : R[X]`, then `(p * q).content = p.content * q.content`.
- `Polynomial.NormalizedGcdMonoid`: the polynomial ring of a GCD domain is itself a GCD domain.

## Note

This has nothing to do with minimal polynomials of primitive elements in finite fields.

-/

namespace Polynomial

section Primitive

variable {R : Type*} [CommSemiring R]

def IsPrimitive (p : R[X]) : Prop :=
  ∀ r : R, C r ∣ p → IsUnit r
