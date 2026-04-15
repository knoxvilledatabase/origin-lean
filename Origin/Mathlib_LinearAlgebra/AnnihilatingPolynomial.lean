/-
Extracted from LinearAlgebra/AnnihilatingPolynomial.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Annihilating Ideal

Given a commutative ring `R` and an `R`-algebra `A`,
every element `a : A` defines
an ideal `Polynomial.annIdeal a ⊆ R[X]`.
Simply put, this is the set of polynomials `p` where
the polynomial evaluation `p(a)` is 0.

## Special case where the ground ring is a field

In the special case that `R` is a field, we use the notation `R = 𝕜`.
Here `𝕜[X]` is a PID, so there is a polynomial `g ∈ Polynomial.annIdeal a`
which generates the ideal. We show that if this generator is
chosen to be monic, then it is the minimal polynomial of `a`,
as defined in `FieldTheory.Minpoly`.

## Special case: endomorphism algebra

Given an `R`-module `M` (`[AddCommGroup M] [Module R M]`)
there are some common specializations which may be more familiar.
* Example 1: `A = M →ₗ[R] M`, the endomorphism algebra of an `R`-module M.
* Example 2: `A = n × n` matrices with entries in `R`.
-/

open Polynomial

namespace Polynomial

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (R) in

noncomputable def annIdeal (a : A) : Ideal R[X] :=
  RingHom.ker ((aeval a).toRingHom : R[X] →+* A)

end Semiring

section Field

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

variable (𝕜)

open Submodule

noncomputable def annIdealGenerator (a : A) : 𝕜[X] :=
  let g := IsPrincipal.generator <| annIdeal 𝕜 a
  g * C g.leadingCoeff⁻¹

variable {𝕜}
