/-
Extracted from Algebra/MvPolynomial/Counit.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
## Counit morphisms for multivariate polynomials

One may consider the ring of multivariate polynomials `MvPolynomial A R` with coefficients in `R`
and variables indexed by `A`. If `A` is not just a type, but an algebra over `R`,
then there is a natural surjective algebra homomorphism `MvPolynomial A R →ₐ[R] A`
obtained by `X a ↦ a`.

### Main declarations

* `MvPolynomial.ACounit R A` is the natural surjective algebra homomorphism
  `MvPolynomial A R →ₐ[R] A` obtained by `X a ↦ a`
* `MvPolynomial.counit` is an “absolute” variant with `R = ℤ`
* `MvPolynomial.counitNat` is an “absolute” variant with `R = ℕ`

-/

namespace MvPolynomial

open Function

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

noncomputable def ACounit : MvPolynomial B A →ₐ[A] B :=
  aeval id

variable {B}
