/-
Extracted from RingTheory/Coprime/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Coprime elements of a ring or monoid

## Main definition

* `IsCoprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
  that `a * x + b * y = 1`. Note that elements with no common divisors (`IsRelPrime`) are not
  necessarily coprime, e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.
  The two notions are equivalent in Bézout rings, see `isRelPrime_iff_isCoprime`.

This file also contains lemmas about `IsRelPrime` parallel to `IsCoprime`.

See also `RingTheory.Coprime.Lemmas` for further development of coprime elements.
-/

universe u v

section CommSemiring

variable {R : Type u} [CommSemiring R] (x y z w : R)

def IsCoprime : Prop :=
  ∃ a b, a * x + b * y = 1

variable {x y z w}
