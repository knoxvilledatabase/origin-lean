/-
Extracted from RingTheory/Polynomial/Chebyshev.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chebyshev polynomials

The Chebyshev polynomials are families of polynomials indexed by `ℤ`,
with integral coefficients.

## Main definitions

* `Polynomial.Chebyshev.T`: the Chebyshev polynomials of the first kind.
* `Polynomial.Chebyshev.U`: the Chebyshev polynomials of the second kind.
* `Polynomial.Chebyshev.C`: the rescaled Chebyshev polynomials of the first kind (also known as the
  Vieta–Lucas polynomials), given by $C_n(2x) = 2T_n(x)$.
* `Polynomial.Chebyshev.S`: the rescaled Chebyshev polynomials of the second kind (also known as the
  Vieta–Fibonacci polynomials), given by $S_n(2x) = U_n(x)$.

## Main statements

* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.
* `Polynomial.Chebyshev.T_mul_T`, twice the product of the `m`-th and `k`-th Chebyshev polynomials
  of the first kind is the sum of the `m + k`-th and `m - k`-th Chebyshev polynomials of the first
  kind. There is a similar statement `Polynomial.Chebyshev.C_mul_C` for the `C` polynomials.
* `Polynomial.Chebyshev.T_mul`, the `(m * n)`-th Chebyshev polynomial of the first kind is the
  composition of the `m`-th and `n`-th Chebyshev polynomials of the first kind. There is a similar
  statement `Polynomial.Chebyshev.C_mul` for the `C` polynomials.

## Implementation details

Since Chebyshev polynomials have interesting behaviour over the complex numbers and modulo `p`,
we define them to have coefficients in an arbitrary commutative ring, even though
technically `ℤ` would suffice.
The benefit of allowing arbitrary coefficient rings, is that the statements afterwards are clean,
and do not have `map (Int.castRingHom R)` interfering all the time.

## References

[Lionel Ponton, _Roots of the Chebyshev polynomials: A purely algebraic approach_]
[ponton2020chebyshev]

## TODO

* Redefine and/or relate the definition of Chebyshev polynomials to `LinearRecurrence`.
* Add explicit formula involving square roots for Chebyshev polynomials
-/

namespace Polynomial.Chebyshev

open Polynomial

variable (R R' : Type*) [CommRing R] [CommRing R']

noncomputable def T : ℤ → R[X]
  | 0 => 1
  | 1 => X
  | (n : ℕ) + 2 => 2 * X * T (n + 1) - T n
  | -((n : ℕ) + 1) => 2 * X * T (-n) - T (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)
