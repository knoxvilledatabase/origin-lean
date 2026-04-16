/-
Extracted from NumberTheory/ModularForms/QExpansion.lean
Genuine: 6 | Conflates: 0 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Complex.Periodic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.Identities

noncomputable section

/-!
# q-expansions of modular forms

We show that a modular form of level `Γ(n)` can be written as `τ ↦ F (𝕢 n τ)` where `F` is
analytic on the open unit disc, and `𝕢 n` is the parameter `τ ↦ exp (2 * I * π * τ / n)`. As an
application, we show that cusp forms decay exponentially to 0 as `im τ → ∞`.

## TO DO:

* generalise to handle arbitrary finite-index subgroups (not just `Γ(n)` for some `n`)
* define the `q`-expansion as a formal power series
-/

open ModularForm Complex Filter Asymptotics UpperHalfPlane Function

open scoped Real Topology Manifold MatrixGroups CongruenceSubgroup

noncomputable section

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

local notation "I∞" => comap Complex.im atTop

local notation "𝕢" => Periodic.qParam

theorem Function.Periodic.im_invQParam_pos_of_abs_lt_one
    {h : ℝ} (hh : 0 < h) {q : ℂ} (hq : q.abs < 1) (hq_ne : q ≠ 0) :
    0 < im (Periodic.invQParam h q) :=
  im_invQParam .. ▸ mul_pos_of_neg_of_neg
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) Real.two_pi_pos)
    ((Real.log_neg_iff (Complex.abs.pos hq_ne)).mpr hq)

namespace SlashInvariantFormClass

theorem periodic_comp_ofComplex [SlashInvariantFormClass F Γ(n) k] :
    Periodic (f ∘ ofComplex) n := by
  intro w
  by_cases hw : 0 < im w
  · have : 0 < im (w + n) := by simp only [add_im, natCast_im, add_zero, hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert SlashInvariantForm.vAdd_width_periodic n k 1 f ⟨w, hw⟩ using 2
    simp only [Int.cast_one, mul_one, UpperHalfPlane.ext_iff, coe_mk_subtype, coe_vadd,
      ofReal_natCast, add_comm]
  · have : im (w + n) ≤ 0 := by simpa only [add_im, natCast_im, add_zero, not_lt] using hw
    simp only [comp_apply, ofComplex_apply_of_im_nonpos this,
      ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

def cuspFunction : ℂ → ℂ := Function.Periodic.cuspFunction n (f ∘ ofComplex)

-- DISSOLVED: eq_cuspFunction

end SlashInvariantFormClass

open SlashInvariantFormClass

namespace ModularFormClass

theorem differentiableAt_comp_ofComplex [ModularFormClass F Γ k] {z : ℂ} (hz : 0 < im z) :
    DifferentiableAt ℂ (f ∘ ofComplex) z :=
  mdifferentiableAt_iff_differentiableAt.mp ((holo f _).comp z (mdifferentiableAt_ofComplex hz))

theorem bounded_at_infty_comp_ofComplex [ModularFormClass F Γ k] :
    BoundedAtFilter I∞ (f ∘ ofComplex) := by
  simpa only [SlashAction.slash_one, ModularForm.toSlashInvariantForm_coe]
    using (ModularFormClass.bdd_at_infty f 1).comp_tendsto tendsto_comap_im_ofComplex

-- DISSOLVED: differentiableAt_cuspFunction

-- DISSOLVED: analyticAt_cuspFunction_zero

end ModularFormClass

open ModularFormClass

namespace CuspFormClass

theorem zero_at_infty_comp_ofComplex [CuspFormClass F Γ k] : ZeroAtFilter I∞ (f ∘ ofComplex) := by
  simpa only [SlashAction.slash_one, toSlashInvariantForm_coe]
    using (zero_at_infty f 1).comp tendsto_comap_im_ofComplex

-- DISSOLVED: cuspFunction_apply_zero

-- DISSOLVED: exp_decay_atImInfty

end CuspFormClass
