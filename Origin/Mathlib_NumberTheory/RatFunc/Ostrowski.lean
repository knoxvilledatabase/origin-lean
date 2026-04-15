/-
Extracted from NumberTheory/RatFunc/Ostrowski.lean
Genuine: 2 of 6 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ostrowski's theorem for `K(X)`

This file proves Ostrowski's theorem for the field of rational functions `K(X)`, where `K` is any
field: if `v` is a discrete valuation on `K(X)` which is trivial on elements of `K`, then `v` is
equivalent to either the `I`-adic valuation for some `I : HeightOneSpectrum K[X]`, or to the
valuation at infinity `FunctionField.inftyValuation K`.

## Main results
- `RatFunc.valuation_isEquiv_infty_or_adic`: Ostrowski's theorem for `K(X)`.
-/

open Multiplicative WithZero

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation (RatFunc K) Γ}

namespace RatFunc

section Infinity

open FunctionField Polynomial Valuation

-- DISSOLVED: valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X

variable [DecidableEq (RatFunc K)]

lemma valuation_isEquiv_inftyValuation_of_one_lt_valuation_X [v.IsTrivialOn K] (hlt : 1 < v X) :
    v.IsEquiv (inftyValuation K) := by
  refine isEquiv_iff_val_lt_one.mpr fun {f} ↦ ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hlt' : 1 < inftyValuation K X := by simp [← exp_zero]
    rw [valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X hlt hf,
      valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X hlt' hf]
    grind [one_le_zpow_iff_right₀]

end Infinity

open IsDedekindDomain HeightOneSpectrum Set Valuation FunctionField Polynomial

-- DISSOLVED: setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty

-- DISSOLVED: one_le_valuation_factor

-- DISSOLVED: irreducible_min_polynomial_valuation_lt_one_and_ne_zero

section valuation_X_le_one

variable [v.IsNontrivial] [v.IsTrivialOn K] (hle : v RatFunc.X ≤ 1)

abbrev uniformizingPolynomial : K[X] :=
  WellFounded.min degree_lt_wf _ (setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)
