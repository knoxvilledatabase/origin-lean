/-
Extracted from RingTheory/Valuation/Minpoly.lean
Genuine: 1 | Conflates: 0 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Valuation.Basic

/-!
# Minimal polynomials.

We prove some results about valuations of zero coefficients of minimal polynomials.

Let `K` be a field with a valuation `v` and let `L` be a field extension of `K`.

# Main Results
* `coeff_zero_minpoly` : for `x ∈ K` the valuation of the zeroth coefficient of the minimal
  polynomial of `algebra_map K L x` over `K` is equal to the valuation of `x`.
* `pow_coeff_zero_ne_zero_of_unit` : for any unit `x : Lˣ`, we prove that a certain power of the
  valuation of zeroth coefficient of the minimal polynomial of `x` over `K` is nonzero. This lemma
  is helpful for defining the valuation on `L` inducing `v`.
-/

open Module minpoly Polynomial

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (L : Type*) [Field L] [Algebra K L]

namespace Valuation

@[simp]
theorem coeff_zero_minpoly (x : K) : v ((minpoly K (algebraMap K L x)).coeff 0) = v x := by
  rw [minpoly.eq_X_sub_C, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, Valuation.map_neg]

variable {L}

-- DISSOLVED: pow_coeff_zero_ne_zero_of_unit

end Valuation
