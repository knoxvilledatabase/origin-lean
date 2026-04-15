/-
Extracted from Algebra/Polynomial/Expand.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

## Main definitions

* `Polynomial.expand R p f`: expand the polynomial `f` with coefficients in a
  commutative semiring `R` by a factor of p, so `expand R p (∑ aₙ xⁿ)` is `∑ aₙ xⁿᵖ`.
* `Polynomial.contract p f`: the opposite of `expand`, so it sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.

-/

universe u v w

open Polynomial

open Finset

namespace Polynomial

section CommSemiring

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

noncomputable def expand : R[X] →ₐ[R] R[X] :=
  { (eval₂RingHom C (X ^ p) : R[X] →+* R[X]) with commutes' := fun _ => eval₂_C _ _ }

variable {R}

theorem expand_eq_sum {f : R[X]} : expand R p f = f.sum fun e a => C a * (X ^ p) ^ e := by
  simp [expand, eval₂]
