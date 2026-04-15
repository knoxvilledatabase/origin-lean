/-
Extracted from Algebra/Polynomial/Mirror.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# "Mirror" of a univariate polynomial

In this file we define `Polynomial.mirror`, a variant of `Polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`.

## Main definitions

- `Polynomial.mirror`

## Main results

- `Polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `Polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`

-/

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] (p q : R[X])

noncomputable def mirror :=
  p.reverse * X ^ p.natTrailingDegree
