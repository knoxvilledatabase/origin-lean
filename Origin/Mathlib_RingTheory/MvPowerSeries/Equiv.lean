/-
Extracted from RingTheory/MvPowerSeries/Equiv.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivalences related to power series rings

This file establishes a number of equivalences related to power series rings.

* `MvPowerSeries.toAdicCompletionAlgEquiv` : the canonical isomorphism from
  multivariate power series to the adic completion of multivariate polynomials
  with respect to the ideal spanned by all variables when the index is finite.

-/

noncomputable section

namespace MvPowerSeries

section toAdicCompletion

open Finsupp

variable {σ R : Type*} {n : ℕ} [CommRing R] [Finite σ]

lemma truncTotal_sub_truncTotal_mem_pow_idealOfVars {l m n : ℕ} (h : l ≤ m) (h' : l ≤ n)
    (p : MvPowerSeries σ R) : (truncTotal R m) p - (truncTotal R n) p ∈
      MvPolynomial.idealOfVars σ R ^ l := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx ↦ ?_)
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ (by lia),
    coeff_truncTotal _ (by lia)]

lemma truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars (p q : MvPowerSeries σ R) :
    (truncTotal R n) (p * q) - (truncTotal R n) p * (truncTotal R n) q ∈
      MvPolynomial.idealOfVars σ R ^ n := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx ↦ ?_)
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ hx,
    coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hx]
