/-
Extracted from RingTheory/PowerSeries/WellKnown.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definition of well-known power series

In this file we define the following power series:

* `PowerSeries.invUnitsSub`: given `u : Rˣ`, this is the series for `1 / (u - x)`.
  It is given by `∑ n, x ^ n /ₚ u ^ (n + 1)`.

* `PowerSeries.invOneSubPow`: given a commutative ring `S` and a number `d : ℕ`,
  `PowerSeries.invOneSubPow S d` is the multiplicative inverse of `(1 - X) ^ d` in `S⟦X⟧ˣ`.
  When `d` is `0`, `PowerSeries.invOneSubPow S d` will just be `1`. When `d` is positive,
  `PowerSeries.invOneSubPow S d` will be `∑ n, Nat.choose (d - 1 + n) (d - 1)`.

* `PowerSeries.sin`, `PowerSeries.cos`, `PowerSeries.exp` : power series for sin, cosine, and
  exponential functions.
-/

namespace PowerSeries

section Ring

variable {R S : Type*} [Ring R] [Ring S]

def invUnitsSub (u : Rˣ) : PowerSeries R :=
  mk fun n => 1 /ₚ u ^ (n + 1)
