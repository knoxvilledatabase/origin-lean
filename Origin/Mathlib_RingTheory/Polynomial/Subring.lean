/-
Extracted from RingTheory/Polynomial/Subring.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Polynomials over subrings

Given a ring `K` with a subring `R`, we construct a map from polynomials in `K[X]` with coefficients
in `R` to `R[X]`. We provide several lemmas to deal with coefficients, degree, and evaluation of
`Polynomial.toSubring`.

## Main Definitions

* `Polynomial.toSubring` : given a polynomial `P` in `K[X]` whose coefficients all belong to a
  subring `R` of the ring `K`, `P.toSubring R` is the corresponding polynomial in `R[X]`.
-/

namespace Polynomial

variable {R : Type*} [Ring R] (p : R[X]) (T : Subring R)

noncomputable def toSubring (hp : (↑p.coeffs : Set R) ⊆ T) : T[X] :=
  ∑ i ∈ p.support,
    monomial i
      (⟨p.coeff i,
        letI := Classical.decEq R
        if H : p.coeff i = 0 then H.symm ▸ T.zero_mem else hp (p.coeff_mem_coeffs H)⟩ : T)

variable (hp : (↑p.coeffs : Set R) ⊆ T)
