/-
Extracted from Analysis/Complex/UpperHalfPlane/Exp.lean
Genuine: 2 of 4 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exp on the upper half plane

This file contains lemmas about the exponential function on the upper half plane. Useful for
q-expansions of modular forms.
-/

open Real Complex UpperHalfPlane Function

local notation "𝕢" => Periodic.qParam

-- DISSOLVED: Function.Periodic.im_invQParam_pos_of_norm_lt_one

lemma Function.Periodic.norm_qParam_le_of_one_half_le_im {ξ : ℂ} (hξ : 1 / 2 ≤ ξ.im) :
    ‖𝕢 1 ξ‖ ≤ rexp (-π) := by
  rwa [Periodic.qParam, ofReal_one, div_one, Complex.norm_exp, Real.exp_le_exp,
    mul_right_comm, mul_I_re, neg_le_neg_iff, ← ofReal_ofNat, ← ofReal_mul, im_ofReal_mul,
    mul_comm _ π, mul_assoc, le_mul_iff_one_le_right Real.pi_pos, ← div_le_iff₀' two_pos]

-- DISSOLVED: UpperHalfPlane.norm_qParam_lt_one

theorem UpperHalfPlane.norm_exp_two_pi_I_lt_one (τ : ℍ) :
    ‖(Complex.exp (2 * π * Complex.I * τ))‖ < 1 := by
  simpa [Function.Periodic.norm_qParam, Complex.norm_exp] using τ.norm_qParam_lt_one 1
