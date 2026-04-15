/-
Extracted from RingTheory/MvPolynomial/Expand.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results on `MvPolynomial.expand`

In this file we prove results about `MvPolynomial.expand` that require more than the basic API
available in `Mathlib.Algebra.*`.
-/

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] (p : ℕ) [ExpChar R p]

theorem map_frobenius_expand {f : MvPolynomial σ R} :
    (f.expand p).map (frobenius R p) = f ^ p :=
  f.induction_on' fun _ _ => by simp [monomial_pow, frobenius]
    fun _ _ ha hb => by rw [map_add, map_add, ha, hb, add_pow_expChar]
