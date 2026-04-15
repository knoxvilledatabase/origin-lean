/-
Extracted from Algebra/Ring/Subring/IntPolynomial.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Polynomials over subrings.

Given a field `K` with a subring `R`, in this file we construct a map from polynomials in `K[X]`
with coefficients in `R` to `R[X]`. We provide several lemmas to deal with
coefficients, degree, and evaluation of `Polynomial.int`.
This is useful when dealing with integral elements in an extension of fields.

## Main Definitions
* `Polynomial.int` : given a polynomial `P` in `K[X]` whose coefficients all belong to a subring `R`
  of the field `K`, `P.int R` is the corresponding polynomial in `R[X]`.
-/

variable {K : Type*} [Field K] (R : Subring K)

open scoped Polynomial

def Polynomial.int (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R) : R[X] where
  toFinsupp :=
  { support := P.support
    toFun := fun n => ⟨P.coeff n, hP n⟩
    mem_support_toFun := fun n => by
      rw [ne_eq, ← Subring.coe_eq_zero_iff, mem_support_iff] }

namespace Polynomial

variable (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R)
