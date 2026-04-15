/-
Extracted from Algebra/Polynomial/Taylor.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Taylor expansions of polynomials

## Main declarations

* `Polynomial.taylor`: the Taylor expansion of the polynomial `f` at `r`
* `Polynomial.taylor_coeff`: the `k`th coefficient of `taylor r f` is
  `(Polynomial.hasseDeriv k f).eval r`
* `Polynomial.eq_zero_of_hasseDeriv_eq_zero`:
  the identity principle: a polynomial is 0 iff all its Hasse derivatives are zero

-/

noncomputable section

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

def taylor (r : R) : R[X] →ₗ[R] R[X] where
  toFun f := f.comp (X + C r)
  map_add' _ _ := add_comp
  map_smul' c f := by simp only [smul_eq_C_mul, C_mul_comp, RingHom.id_apply]
