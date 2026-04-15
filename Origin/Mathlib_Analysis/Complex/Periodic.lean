/-
Extracted from Analysis/Complex/Periodic.lean
Genuine: 5 of 8 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Periodic holomorphic functions

We show that if `f : ℂ → ℂ` satisfies `f (z + h) = f z`, for some nonzero real `h`, then there is a
function `F` such that `f z = F (exp (2 * π * I * z / h))` for all `z`; and if `f` is holomorphic
at some `z`, then `F` is holomorphic at `exp (2 * π * I * z / h)`.

We also show (using Riemann's removable singularity theorem) that if `f` is holomorphic and bounded
for all sufficiently large `im z`, then `F` extends to a holomorphic function on a neighbourhood of
`0`. As a consequence, if `f` tends to zero as `im z → ∞`, then in fact it decays *exponentially*
to zero. These results are important in the theory of modular forms.
-/

open Complex Filter Asymptotics

open scoped Real Topology

noncomputable section

local notation "I∞" => comap im atTop

variable (h : ℝ)

namespace Function.Periodic

def qParam (z : ℂ) : ℂ := exp (2 * π * I * z / h)

def invQParam (q : ℂ) : ℂ := h / (2 * π * I) * log q

local notation "𝕢" => qParam

section qParam

theorem norm_qParam (z : ℂ) : ‖𝕢 h z‖ = Real.exp (-2 * π * im z / h) := by
  simp only [qParam, norm_exp, div_ofReal_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, zero_sub,
    neg_mul]

theorem im_invQParam (q : ℂ) : im (invQParam h q) = -h / (2 * π) * Real.log ‖q‖ := by
  simp only [invQParam, ← div_div, div_I, neg_mul, neg_im, mul_im, mul_re, div_ofReal_re,
    div_ofNat_re, ofReal_re, I_re, mul_zero, div_ofReal_im, div_ofNat_im, ofReal_im, zero_div, I_im,
    mul_one, sub_self, zero_mul, add_zero, log_re, zero_add, neg_div]

variable {h} -- next few theorems all assume h ≠ 0 or 0 < h

-- DISSOLVED: qParam_right_inv

-- DISSOLVED: qParam_left_inv_mod_period

theorem norm_qParam_lt_iff (hh : 0 < h) (A : ℝ) (z : ℂ) :
    ‖qParam h z‖ < Real.exp (-2 * π * A / h) ↔ A < im z := by
  rw [norm_qParam, Real.exp_lt_exp, div_lt_div_iff_of_pos_right hh, mul_lt_mul_left_of_neg]
  simpa using Real.pi_pos

-- DISSOLVED: qParam_ne_zero
