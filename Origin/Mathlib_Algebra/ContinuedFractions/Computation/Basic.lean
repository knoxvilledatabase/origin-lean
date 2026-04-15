/-
Extracted from Algebra/ContinuedFractions/Computation/Basic.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Computable Continued Fractions

## Summary

We formalise the standard computation of (regular) continued fractions for linear ordered floor
fields. The algorithm is rather simple. Here is an outline of the procedure adapted from Wikipedia:

Take a value `v`. We call `⌊v⌋` the *integer part* of `v` and `v - ⌊v⌋` the *fractional part* of
`v`.  A continued fraction representation of `v` can then be given by `[⌊v⌋; b₀, b₁, b₂,...]`, where
`[b₀; b₁, b₂,...]` recursively is the continued fraction representation of `1 / (v - ⌊v⌋)`.  This
process stops when the fractional part hits 0.

In other words: to calculate a continued fraction representation of a number `v`, write down the
integer part (i.e. the floor) of `v`. Subtract this integer part from `v`. If the difference is 0,
stop; otherwise find the reciprocal of the difference and repeat. The procedure will terminate if
and only if `v` is rational.

For an example, refer to `IntFractPair.stream`.

## Main definitions

- `GenContFract.IntFractPair.stream`: computes the stream of integer and fractional parts of a given
  value as described in the summary.
- `GenContFract.of`: computes the generalised continued fraction of a value `v`.
  In fact, it computes a regular continued fraction that terminates if and only if `v` is rational.

## Implementation Notes

There is an intermediate definition `GenContFract.IntFractPair.seq1` between
`GenContFract.IntFractPair.stream` and `GenContFract.of` to wire up things. Users should not
(need to) directly interact with it.

The computation of the integer and fractional pairs of a value can elegantly be
captured by a recursive computation of a stream of option pairs. This is done in
`IntFractPair.stream`. However, the type then does not guarantee the first pair to always be
`some` value, as expected by a continued fraction.

To separate concerns, we first compute a single head term that always exists in
`GenContFract.IntFractPair.seq1` followed by the remaining stream of option pairs. This sequence
with a head term (`seq1`) is then transformed to a generalized continued fraction in
`GenContFract.of` by extracting the wanted integer parts of the head term and the stream.

## References

- https://en.wikipedia.org/wiki/Continued_fraction

## Tags

numerics, number theory, approximations, fractions
-/

assert_not_exists Finset

namespace GenContFract

variable (K : Type*)

structure IntFractPair where
  b : ℤ
  fr : K

variable {K}

/-! Interlude: define some expected coercions and instances. -/

namespace IntFractPair

-- INSTANCE (free from Core): [Repr

-- INSTANCE (free from Core): inhabited

def mapFr {β : Type*} (f : K → β) (gp : IntFractPair K) : IntFractPair β :=
  ⟨gp.b, f gp.fr⟩

section coe

/-! Interlude: define some expected coercions. -/

variable {β : Type*} [Coe K β]
