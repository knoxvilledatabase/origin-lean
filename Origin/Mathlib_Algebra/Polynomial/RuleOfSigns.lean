/-
Extracted from Algebra/Polynomial/RuleOfSigns.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Descartes' Rule of Signs

We define the "sign changes" in the coefficients of a polynomial, and prove Descartes'
Rule of Signs: a real polynomial has at most as many positive roots as there are sign
changes. A sign change is when there is a positive coefficient followed by a negative
coefficient, or vice versa, with any number of zero coefficients in between.

## Main Definitions

- `Polynomial.signVariations`: The number of sign changes in a polynomial's coefficients,
  where `0` coefficients are ignored.

## Main theorem

- `Polynomial.roots_countP_pos_le_signVariations`. States that
  `P.roots.countP (0 < ·) ≤ P.signVariations`, so that positive roots are counted with multiplicity.
  It's currently proved for any `CommRing` with `IsStrictOrderedRing`. There is likely some correct
  statement in terms of a (noncommutative) `Ring`, but `Polynomial.roots` is only defined for
  commutative rings.

## Reference

[Wikipedia: Descartes' Rule of Signs](https://en.wikipedia.org/wiki/Descartes%27_rule_of_signs)
-/

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

def signVariations : ℕ :=
  letI coeff_signs := (coeffList P).map SignType.sign
  letI nonzero_signs := coeff_signs.filter (· ≠ 0)
  (nonzero_signs.destutter (· ≠ ·)).length - 1

variable (R) in
