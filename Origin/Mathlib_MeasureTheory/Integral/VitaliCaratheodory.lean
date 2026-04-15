/-
Extracted from MeasureTheory/Integral/VitaliCaratheodory.lean
Genuine: 4 of 10 | Dissolved: 6 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Semicontinuous
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.Instances.EReal

/-!
# Vitali-Carathéodory theorem

Vitali-Carathéodory theorem asserts the following. Consider an integrable function `f : α → ℝ` on
a space with a regular measure. Then there exists a function `g : α → EReal` such that `f x < g x`
everywhere, `g` is lower semicontinuous, and the integral of `g` is arbitrarily close to that of
`f`. This theorem is proved in this file, as `exists_lt_lower_semicontinuous_integral_lt`.

Symmetrically, there exists `g < f` which is upper semicontinuous, with integral arbitrarily close
to that of `f`. It follows from the previous statement applied to `-f`. It is formalized under
the name `exists_upper_semicontinuous_lt_integral_gt`.

The most classical version of Vitali-Carathéodory theorem only ensures a large inequality
`f x ≤ g x`. For applications to the fundamental theorem of calculus, though, the strict inequality
`f x < g x` is important. Therefore, we prove the stronger version with strict inequalities in this
file. There is a price to pay: we require that the measure is `σ`-finite, which is not necessary for
the classical Vitali-Carathéodory theorem. Since this is satisfied in all applications, this is
not a real problem.

## Sketch of proof

Decomposing `f` as the difference of its positive and negative parts, it suffices to show that a
positive function can be bounded from above by a lower semicontinuous function, and from below
by an upper semicontinuous function, with integrals close to that of `f`.

For the bound from above, write `f` as a series `∑' n, cₙ * indicator (sₙ)` of simple functions.
Then, approximate `sₙ` by a larger open set `uₙ` with measure very close to that of `sₙ` (this is
possible by regularity of the measure), and set `g = ∑' n, cₙ * indicator (uₙ)`. It is
lower semicontinuous as a series of lower semicontinuous functions, and its integral is arbitrarily
close to that of `f`.

For the bound from below, use finitely many terms in the series, and approximate `sₙ` from inside by
a closed set `Fₙ`. Then `∑ n < N, cₙ * indicator (Fₙ)` is bounded from above by `f`, it is
upper semicontinuous as a finite sum of upper semicontinuous functions, and its integral is
arbitrarily close to that of `f`.

The main pain point in the implementation is that one needs to jump between the spaces `ℝ`, `ℝ≥0`,
`ℝ≥0∞` and `EReal` (and be careful that addition is not well behaved on `EReal`), and between
`lintegral` and `integral`.

We first show the bound from above for simple functions and the nonnegative integral
(this is the main nontrivial mathematical point), then deduce it for general nonnegative functions,
first for the nonnegative integral and then for the Bochner integral.

Then we follow the same steps for the lower bound.

Finally, we glue them together to obtain the main statement
`exists_lt_lower_semicontinuous_integral_lt`.

## Related results

Are you looking for a result on approximation by continuous functions (not just semicontinuous)?
See result `MeasureTheory.Lp.boundedContinuousFunction_dense`, in the file
`Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`.

## References

[Rudin, *Real and Complex Analysis* (Theorem 2.24)][rudin2006real]

-/

open scoped ENNReal NNReal

open MeasureTheory MeasureTheory.Measure

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] (μ : Measure α)
  [WeaklyRegular μ]

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

/-! ### Lower semicontinuous upper bound for nonnegative functions -/

-- DISSOLVED: SimpleFunc.exists_le_lowerSemicontinuous_lintegral_ge

-- DISSOLVED: exists_le_lowerSemicontinuous_lintegral_ge

-- DISSOLVED: exists_lt_lowerSemicontinuous_lintegral_ge

-- DISSOLVED: exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable

variable {μ}

theorem exists_lt_lowerSemicontinuous_integral_gt_nnreal [SigmaFinite μ] (f : α → ℝ≥0)
    (fint : Integrable (fun x => (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, (f x : ℝ≥0∞) < g x) ∧
      LowerSemicontinuous g ∧
      (∀ᵐ x ∂μ, g x < ⊤) ∧
      Integrable (fun x => (g x).toReal) μ ∧ (∫ x, (g x).toReal ∂μ) < (∫ x, ↑(f x) ∂μ) + ε := by
  have fmeas : AEMeasurable f μ := by
    convert fint.aestronglyMeasurable.real_toNNReal.aemeasurable
    simp only [Real.toNNReal_coe]
  lift ε to ℝ≥0 using εpos.le
  obtain ⟨δ, δpos, hδε⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ δ < ε := exists_between εpos
  have int_f_ne_top : (∫⁻ a : α, f a ∂μ) ≠ ∞ :=
    (hasFiniteIntegral_iff_ofNNReal.1 fint.hasFiniteIntegral).ne
  rcases exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable μ f fmeas
      (ENNReal.coe_ne_zero.2 δpos.ne') with
    ⟨g, f_lt_g, gcont, gint⟩
  have gint_ne : (∫⁻ x : α, g x ∂μ) ≠ ∞ := ne_top_of_le_ne_top (by simpa) gint
  have g_lt_top : ∀ᵐ x : α ∂μ, g x < ∞ := ae_lt_top gcont.measurable gint_ne
  have Ig : (∫⁻ a : α, ENNReal.ofReal (g a).toReal ∂μ) = ∫⁻ a : α, g a ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [g_lt_top] with _ hx
    simp only [hx.ne, ENNReal.ofReal_toReal, Ne, not_false_iff]
  refine ⟨g, f_lt_g, gcont, g_lt_top, ?_, ?_⟩
  · refine ⟨gcont.measurable.ennreal_toReal.aemeasurable.aestronglyMeasurable, ?_⟩
    simp only [hasFiniteIntegral_iff_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    convert gint_ne.lt_top using 1
  · rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
    · calc
        ENNReal.toReal (∫⁻ a : α, ENNReal.ofReal (g a).toReal ∂μ) =
            ENNReal.toReal (∫⁻ a : α, g a ∂μ) := by congr 1
        _ ≤ ENNReal.toReal ((∫⁻ a : α, f a ∂μ) + δ) := by
          apply ENNReal.toReal_mono _ gint
          simpa using int_f_ne_top
        _ = ENNReal.toReal (∫⁻ a : α, f a ∂μ) + δ := by
          rw [ENNReal.toReal_add int_f_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal]
        _ < ENNReal.toReal (∫⁻ a : α, f a ∂μ) + ε := add_lt_add_left hδε _
        _ = (∫⁻ a : α, ENNReal.ofReal ↑(f a) ∂μ).toReal + ε := by simp

    · apply Filter.Eventually.of_forall fun x => _; simp
    · exact fmeas.coe_nnreal_real.aestronglyMeasurable
    · apply Filter.Eventually.of_forall fun x => _; simp
    · apply gcont.measurable.ennreal_toReal.aemeasurable.aestronglyMeasurable

/-! ### Upper semicontinuous lower bound for nonnegative functions -/

-- DISSOLVED: SimpleFunc.exists_upperSemicontinuous_le_lintegral_le

-- DISSOLVED: exists_upperSemicontinuous_le_lintegral_le

theorem exists_upperSemicontinuous_le_integral_le (f : α → ℝ≥0)
    (fint : Integrable (fun x => (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → ℝ≥0,
      (∀ x, g x ≤ f x) ∧
      UpperSemicontinuous g ∧
      Integrable (fun x => (g x : ℝ)) μ ∧ (∫ x, (f x : ℝ) ∂μ) - ε ≤ ∫ x, ↑(g x) ∂μ := by
  lift ε to ℝ≥0 using εpos.le
  rw [NNReal.coe_pos, ← ENNReal.coe_pos] at εpos
  have If : (∫⁻ x, f x ∂μ) < ∞ := hasFiniteIntegral_iff_ofNNReal.1 fint.hasFiniteIntegral
  rcases exists_upperSemicontinuous_le_lintegral_le f If.ne εpos.ne' with ⟨g, gf, gcont, gint⟩
  have Ig : (∫⁻ x, g x ∂μ) < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) If
    simpa using gf x
  refine ⟨g, gf, gcont, ?_, ?_⟩
  · refine
      Integrable.mono fint gcont.measurable.coe_nnreal_real.aemeasurable.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by simp [gf x]
  · rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
    · rw [sub_le_iff_le_add]
      convert ENNReal.toReal_mono _ gint
      · simp
      · rw [ENNReal.toReal_add Ig.ne ENNReal.coe_ne_top]; simp
      · simpa using Ig.ne
    · apply Filter.Eventually.of_forall; simp
    · exact gcont.measurable.coe_nnreal_real.aemeasurable.aestronglyMeasurable
    · apply Filter.Eventually.of_forall; simp
    · exact fint.aestronglyMeasurable

/-! ### Vitali-Carathéodory theorem -/

theorem exists_lt_lowerSemicontinuous_integral_lt [SigmaFinite μ] (f : α → ℝ) (hf : Integrable f μ)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → EReal,
      (∀ x, (f x : EReal) < g x) ∧
      LowerSemicontinuous g ∧
      Integrable (fun x => EReal.toReal (g x)) μ ∧
      (∀ᵐ x ∂μ, g x < ⊤) ∧ (∫ x, EReal.toReal (g x) ∂μ) < (∫ x, f x ∂μ) + ε := by
  let δ : ℝ≥0 := ⟨ε / 2, (half_pos εpos).le⟩
  have δpos : 0 < δ := half_pos εpos
  let fp : α → ℝ≥0 := fun x => Real.toNNReal (f x)
  have int_fp : Integrable (fun x => (fp x : ℝ)) μ := hf.real_toNNReal
  rcases exists_lt_lowerSemicontinuous_integral_gt_nnreal fp int_fp δpos with
    ⟨gp, fp_lt_gp, gpcont, gp_lt_top, gp_integrable, gpint⟩
  let fm : α → ℝ≥0 := fun x => Real.toNNReal (-f x)
  have int_fm : Integrable (fun x => (fm x : ℝ)) μ := hf.neg.real_toNNReal
  rcases exists_upperSemicontinuous_le_integral_le fm int_fm δpos with
    ⟨gm, gm_le_fm, gmcont, gm_integrable, gmint⟩
  let g : α → EReal := fun x => (gp x : EReal) - gm x
  have ae_g : ∀ᵐ x ∂μ, (g x).toReal = (gp x : EReal).toReal - (gm x : EReal).toReal := by
    filter_upwards [gp_lt_top] with _ hx
    rw [EReal.toReal_sub] <;> simp [hx.ne]
  refine ⟨g, ?lt, ?lsc, ?int, ?aelt, ?intlt⟩
  case int =>
    show Integrable (fun x => EReal.toReal (g x)) μ
    rw [integrable_congr ae_g]
    convert gp_integrable.sub gm_integrable
    simp
  case intlt =>
    show (∫ x : α, (g x).toReal ∂μ) < (∫ x : α, f x ∂μ) + ε
    exact
      calc
        (∫ x : α, (g x).toReal ∂μ) = ∫ x : α, EReal.toReal (gp x) - EReal.toReal (gm x) ∂μ :=
          integral_congr_ae ae_g
        _ = (∫ x : α, EReal.toReal (gp x) ∂μ) - ∫ x : α, ↑(gm x) ∂μ := by
          simp only [EReal.toReal_coe_ennreal, ENNReal.coe_toReal]
          exact integral_sub gp_integrable gm_integrable
        _ < (∫ x : α, ↑(fp x) ∂μ) + ↑δ - ∫ x : α, ↑(gm x) ∂μ := by
          apply sub_lt_sub_right
          convert gpint
          simp only [EReal.toReal_coe_ennreal]
        _ ≤ (∫ x : α, ↑(fp x) ∂μ) + ↑δ - ((∫ x : α, ↑(fm x) ∂μ) - δ) := sub_le_sub_left gmint _
        _ = (∫ x : α, f x ∂μ) + 2 * δ := by
          simp_rw [integral_eq_integral_pos_part_sub_integral_neg_part hf]; ring
        _ = (∫ x : α, f x ∂μ) + ε := by congr 1; field_simp [δ, mul_comm]
  case aelt =>
    show ∀ᵐ x : α ∂μ, g x < ⊤
    filter_upwards [gp_lt_top] with ?_ hx
    simp only [g, sub_eq_add_neg, Ne, (EReal.add_lt_top _ _).ne, lt_top_iff_ne_top,
      lt_top_iff_ne_top.1 hx, EReal.coe_ennreal_eq_top_iff, not_false_iff, EReal.neg_eq_top_iff,
      EReal.coe_ennreal_ne_bot]
  case lt =>
    show ∀ x, (f x : EReal) < g x
    intro x
    rw [EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (f x)]
    refine EReal.sub_lt_sub_of_lt_of_le ?_ ?_ ?_ ?_
    · simp only [EReal.coe_ennreal_lt_coe_ennreal_iff]; exact fp_lt_gp x
    · simp only [ENNReal.coe_le_coe, EReal.coe_ennreal_le_coe_ennreal_iff]
      exact gm_le_fm x
    · simp only [EReal.coe_ennreal_ne_bot, Ne, not_false_iff]
    · simp only [EReal.coe_nnreal_ne_top, Ne, not_false_iff]
  case lsc =>
    show LowerSemicontinuous g
    apply LowerSemicontinuous.add'
    · exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous gpcont fun x y hxy =>
          EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy
    · apply continuous_neg.comp_upperSemicontinuous_antitone _ fun x y hxy =>
          EReal.neg_le_neg_iff.2 hxy
      dsimp
      apply continuous_coe_ennreal_ereal.comp_upperSemicontinuous _ fun x y hxy =>
          EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy
      exact ENNReal.continuous_coe.comp_upperSemicontinuous gmcont fun x y hxy =>
          ENNReal.coe_le_coe.2 hxy
    · intro x
      exact EReal.continuousAt_add (by simp) (by simp)

theorem exists_upperSemicontinuous_lt_integral_gt [SigmaFinite μ] (f : α → ℝ) (hf : Integrable f μ)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → EReal,
      (∀ x, (g x : EReal) < f x) ∧
      UpperSemicontinuous g ∧
      Integrable (fun x => EReal.toReal (g x)) μ ∧
      (∀ᵐ x ∂μ, ⊥ < g x) ∧ (∫ x, f x ∂μ) < (∫ x, EReal.toReal (g x) ∂μ) + ε := by
  rcases exists_lt_lowerSemicontinuous_integral_lt (fun x => -f x) hf.neg εpos with
    ⟨g, g_lt_f, gcont, g_integrable, g_lt_top, gint⟩
  refine ⟨fun x => -g x, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x => EReal.neg_lt_comm.1 (by simpa only [EReal.coe_neg] using g_lt_f x)
  · exact
      continuous_neg.comp_lowerSemicontinuous_antitone gcont fun x y hxy =>
        EReal.neg_le_neg_iff.2 hxy
  · convert g_integrable.neg
    simp
  · simpa [bot_lt_iff_ne_bot, lt_top_iff_ne_top] using g_lt_top
  · simp_rw [integral_neg, lt_neg_add_iff_add_lt] at gint
    rw [add_comm] at gint
    simpa [integral_neg] using gint

end MeasureTheory
