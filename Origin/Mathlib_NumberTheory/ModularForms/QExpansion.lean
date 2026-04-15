/-
Extracted from NumberTheory/ModularForms/QExpansion.lean
Genuine: 15 of 16 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# q-expansions of modular forms

We show that a modular form of level `Γ(n)` can be written as `τ ↦ F (𝕢 n τ)` where `F` is
analytic on the open unit disc, and `𝕢 n` is the parameter `τ ↦ exp (2 * I * π * τ / n)`. As an
application, we show that cusp forms decay exponentially to 0 as `im τ → ∞`.

We also define the `q`-expansion of a modular form, either as a power series or as a
`FormalMultilinearSeries`, and show that it converges to `f` on the upper half plane.

## Main definitions and results

* `SlashInvariantFormClass.cuspFunction`: for a level `n` slash-invariant form, this is the function
  `F` such that `f τ = F (exp (2 * π * I * τ / n))`, extended by a choice of limit at `0`.
* `ModularFormClass.differentiableAt_cuspFunction`: when `f` is a modular form, its `cuspFunction`
  is differentiable on the open unit disc (including at `0`).
* `ModularFormClass.qExpansion`: the `q`-expansion of a modular form (defined as the Taylor series
  of its `cuspFunction`), bundled as a `PowerSeries`.
* `ModularFormClass.hasSum_qExpansion`: the `q`-expansion evaluated at `𝕢 n τ` sums to `f τ`, for
  `τ` in the upper half plane.
* `qExpansionRingHom` defines the ring homomorphism from the graded ring of modular forms to power
  series given by taking `q`-expansions.
* `qExpansion_coeff_unique` shows that q-expansion coefficients are uniquely determined.

-/

open ModularForm Complex Filter Function Matrix.SpecialLinearGroup Metric Set

open UpperHalfPlane hiding I

open scoped Real MatrixGroups CongruenceSubgroup Topology

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F)

local notation "I∞" => comap Complex.im atTop

local notation "𝕢" => Periodic.qParam

namespace UpperHalfPlane

def valueAtInfty (f : ℍ → ℂ) : ℂ := limUnder atImInfty f

lemma IsZeroAtImInfty.valueAtInfty_eq_zero {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) :
    valueAtInfty f = 0 :=
  hf.limUnder_eq

lemma qParam_tendsto_atImInfty {h : ℝ} (hh : 0 < h) :
    Tendsto (fun τ : ℍ ↦ 𝕢 h τ) atImInfty (nhds 0) :=
  ((Periodic.qParam_tendsto hh).mono_right nhdsWithin_le_nhds).comp tendsto_coe_atImInfty

end UpperHalfPlane

namespace SlashInvariantFormClass

theorem periodic_comp_ofComplex [SlashInvariantFormClass F Γ k] (hΓ : h ∈ Γ.strictPeriods) :
    Periodic (f ∘ ofComplex) h := by
  intro w
  by_cases! hw : 0 < im w
  · have : 0 < im (w + h) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f ⟨w, hw⟩ hΓ using 2
    ext
    simp [add_comm]
  · have : im (w + h) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

variable (h) in

def cuspFunction (f : ℍ → ℂ) : ℂ → ℂ := Function.Periodic.cuspFunction h (f ∘ ofComplex)

-- DISSOLVED: eq_cuspFunction

end SlashInvariantFormClass

open SlashInvariantFormClass

namespace ModularFormClass

theorem differentiableAt_comp_ofComplex [ModularFormClass F Γ k]
      {z : ℂ} (hz : 0 < im z) :
    DifferentiableAt ℂ (f ∘ ofComplex) z :=
  mdifferentiableAt_iff_differentiableAt.mp ((holo f _).comp z (mdifferentiableAt_ofComplex hz))

theorem bounded_at_infty_comp_ofComplex [ModularFormClass F Γ k] (hi : IsCusp OnePoint.infty Γ) :
    BoundedAtFilter I∞ (f ∘ ofComplex) :=
  (OnePoint.isBoundedAt_infty_iff.mp (bdd_at_cusps f hi)).comp_tendsto tendsto_comap_im_ofComplex

theorem differentiableAt_cuspFunction [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspFunction h f) q := by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact (periodic_comp_ofComplex f hΓ).differentiableAt_cuspFunction_zero hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun _ ↦ differentiableAt_comp_ofComplex f))
      (bounded_at_infty_comp_ofComplex f <| Γ.isCusp_of_mem_strictPeriods hh hΓ)
  · exact Periodic.qParam_right_inv hh.ne' hq' ▸
      (periodic_comp_ofComplex f hΓ).differentiableAt_cuspFunction hh.ne'
        <| differentiableAt_comp_ofComplex _ <| Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq'

lemma differentiableOn_cuspFunction_ball [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) :=
  fun _ hz ↦ (differentiableAt_cuspFunction f hh hΓ <| mem_ball_zero_iff.mp hz)
    |>.differentiableWithinAt

lemma analyticAt_cuspFunction_zero [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  DifferentiableOn.analyticAt
    (fun q hq ↦ (differentiableAt_cuspFunction _ hh hΓ hq).differentiableWithinAt)
    (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

lemma cuspFunction_apply_zero [ModularFormClass F Γ k] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    cuspFunction h f 0 = valueAtInfty f := by
  refine (Tendsto.limUnder_eq ?_).symm
  nth_rw 1 [← funext fun τ ↦ eq_cuspFunction f τ hΓ hh.ne']
  refine (analyticAt_cuspFunction_zero f hh hΓ).continuousAt.tendsto.comp ?_
  exact qParam_tendsto_atImInfty hh

variable (h) in

def qExpansion (f : ℍ → ℂ) : PowerSeries ℂ :=
  .mk fun m ↦ (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0

lemma qExpansion_coeff (f : ℍ → ℂ) (m : ℕ) :
    (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0 := by
  simp [qExpansion]

lemma qExpansion_coeff_zero [ModularFormClass F Γ k] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    (qExpansion h f).coeff 0 = valueAtInfty f := by
  simp [qExpansion_coeff, cuspFunction_apply_zero f hh hΓ]

lemma hasSum_qExpansion_of_norm_lt [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m • q ^ m) (cuspFunction h f q) := by
  convert hasSum_taylorSeries_on_ball (differentiableOn_cuspFunction_ball f hh hΓ)
    (by simpa using hq) using 2 with m
  grind [qExpansion_coeff, sub_zero, smul_eq_mul]
