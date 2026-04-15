/-
Extracted from Probability/Distributions/Gaussian.lean
Genuine: 22 | Conflates: 0 | Dissolved: 14 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Decomposition.Lebesgue

/-!
# Gaussian distributions over ℝ

We define a Gaussian measure over the reals.

## Main definitions

* `gaussianPDFReal`: the function `μ v x ↦ (1 / (sqrt (2 * pi * v))) * exp (- (x - μ)^2 / (2 * v))`,
  which is the probability density function of a Gaussian distribution with mean `μ` and
  variance `v` (when `v ≠ 0`).
* `gaussianPDF`: `ℝ≥0∞`-valued pdf, `gaussianPDF μ v x = ENNReal.ofReal (gaussianPDFReal μ v x)`.
* `gaussianReal`: a Gaussian measure on `ℝ`, parametrized by its mean `μ` and variance `v`.
  If `v = 0`, this is `dirac μ`, otherwise it is defined as the measure with density
  `gaussianPDF μ v` with respect to the Lebesgue measure.

## Main results

* `gaussianReal_add_const`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `X + y` is Gaussian with mean `μ + y` and variance `v`.
* `gaussianReal_const_mul`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `c * X` is Gaussian with mean `c * μ` and variance `c^2 * v`.

-/

open scoped ENNReal NNReal Real

open MeasureTheory

namespace ProbabilityTheory

section GaussianPDF

noncomputable

def gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (√(2 * π * v))⁻¹ * rexp (- (x - μ)^2 / (2 * v))

lemma gaussianPDFReal_def (μ : ℝ) (v : ℝ≥0) :
    gaussianPDFReal μ v =
      fun x ↦ (Real.sqrt (2 * π * v))⁻¹ * rexp (- (x - μ)^2 / (2 * v)) := rfl

@[simp]
lemma gaussianPDFReal_zero_var (m : ℝ) : gaussianPDFReal m 0 = 0 := by
  ext1 x
  simp [gaussianPDFReal]

-- DISSOLVED: gaussianPDFReal_pos

lemma gaussianPDFReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ gaussianPDFReal μ v x := by
  rw [gaussianPDFReal]
  positivity

lemma measurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDFReal μ v) :=
  (((measurable_id.add_const _).pow_const _).neg.div_const _).exp.const_mul _

lemma stronglyMeasurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    StronglyMeasurable (gaussianPDFReal μ v) :=
  (measurable_gaussianPDFReal μ v).stronglyMeasurable

lemma integrable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (gaussianPDFReal μ v) := by
  rw [gaussianPDFReal_def]
  by_cases hv : v = 0
  · simp [hv]
  let g : ℝ → ℝ := fun x ↦ (√(2 * π * v))⁻¹ * rexp (- x ^ 2 / (2 * v))
  have hg : Integrable g := by
    suffices g = fun x ↦ (√(2 * π * v))⁻¹ * rexp (- (2 * v)⁻¹ * x ^ 2) by
      rw [this]
      refine (integrable_exp_neg_mul_sq ?_).const_mul (√(2 * π * v))⁻¹
      simp [lt_of_le_of_ne (zero_le _) (Ne.symm hv)]
    ext x
    simp only [g, zero_lt_two, mul_nonneg_iff_of_pos_left, NNReal.zero_le_coe, Real.sqrt_mul',
      mul_inv_rev, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_ofNat, neg_mul, mul_eq_mul_left_iff,
      Real.exp_eq_exp, mul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero, NNReal.coe_eq_zero, hv,
      false_or]
    rw [mul_comm]
    left
    field_simp
  exact Integrable.comp_sub_right hg μ

-- DISSOLVED: lintegral_gaussianPDFReal_eq_one

-- DISSOLVED: integral_gaussianPDFReal_eq_one

lemma gaussianPDFReal_sub {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    gaussianPDFReal μ v (x - y) = gaussianPDFReal (μ + y) v x := by
  simp only [gaussianPDFReal]
  rw [sub_add_eq_sub_sub_swap]

lemma gaussianPDFReal_add {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    gaussianPDFReal μ v (x + y) = gaussianPDFReal (μ - y) v x := by
  rw [sub_eq_add_neg, ← gaussianPDFReal_sub, sub_eq_add_neg, neg_neg]

-- DISSOLVED: gaussianPDFReal_inv_mul

-- DISSOLVED: gaussianPDFReal_mul

noncomputable

def gaussianPDF (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gaussianPDFReal μ v x)

lemma gaussianPDF_def (μ : ℝ) (v : ℝ≥0) :
    gaussianPDF μ v = fun x ↦ ENNReal.ofReal (gaussianPDFReal μ v x) := rfl

@[simp]
lemma gaussianPDF_zero_var (μ : ℝ) : gaussianPDF μ 0 = 0 := by
  ext
  simp [gaussianPDF]

-- DISSOLVED: gaussianPDF_pos

@[measurability]
lemma measurable_gaussianPDF (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDF μ v) :=
  (measurable_gaussianPDFReal _ _).ennreal_ofReal

-- DISSOLVED: lintegral_gaussianPDF_eq_one

end GaussianPDF

section GaussianReal

noncomputable

def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)

-- DISSOLVED: gaussianReal_of_var_ne_zero

@[simp]
lemma gaussianReal_zero_var (μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ := if_pos rfl

instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v) where
  measure_univ := by by_cases h : v = 0 <;> simp [gaussianReal_of_var_ne_zero, h]

-- DISSOLVED: gaussianReal_apply

-- DISSOLVED: gaussianReal_apply_eq_integral

-- DISSOLVED: gaussianReal_absolutelyContinuous

-- DISSOLVED: gaussianReal_absolutelyContinuous'

lemma rnDeriv_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v := by
  by_cases hv : v = 0
  · simp only [hv, gaussianReal_zero_var, gaussianPDF_zero_var]
    refine (Measure.eq_rnDeriv measurable_zero (mutuallySingular_dirac μ volume) ?_).symm
    rw [withDensity_zero, add_zero]
  · rw [gaussianReal_of_var_ne_zero _ hv]
    exact Measure.rnDeriv_withDensity _ (measurable_gaussianPDF μ v)

section Transformations

variable {μ : ℝ} {v : ℝ≥0}

-- DISSOLVED: _root_.MeasurableEmbedding.gaussianReal_comap_apply

-- DISSOLVED: _root_.MeasurableEquiv.gaussianReal_map_symm_apply

lemma gaussianReal_map_add_const (y : ℝ) :
    (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v := by
  by_cases hv : v = 0
  · simp only [hv, ne_eq, not_true, gaussianReal_zero_var]
    exact Measure.map_dirac (measurable_id'.add_const _) _
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ 1) x) x := fun _ ↦ (hasDerivAt_id _).sub_const y
  change (gaussianReal μ v).map e.symm = gaussianReal (μ + y) v
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [abs_neg, abs_one, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, one_mul, ne_eq]
  rw [gaussianReal_apply_eq_integral _ hv s']
  simp [e, gaussianPDFReal_sub _ y, Homeomorph.addRight, ← sub_eq_add_neg]

lemma gaussianReal_map_const_add (y : ℝ) :
    (gaussianReal μ v).map (y + ·) = gaussianReal (μ + y) v := by
  simp_rw [add_comm y]
  exact gaussianReal_map_add_const y

lemma gaussianReal_map_const_mul (c : ℝ) :
    (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  by_cases hv : v = 0
  · simp only [hv, mul_zero, ne_eq, not_true, gaussianReal_zero_var]
    exact Measure.map_dirac (measurable_id'.const_mul c) μ
  by_cases hc : c = 0
  · simp only [hc, zero_mul, ne_eq, abs_zero, mul_eq_zero]
    rw [Measure.map_const]
    simp only [ne_eq, measure_univ, one_smul, mul_eq_zero]
    convert (gaussianReal_zero_var 0).symm
    simp only [ne_eq, zero_pow, mul_eq_zero, hv, or_false, not_false_eq_true, reduceCtorEq]
    rfl
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ c⁻¹) x) x := by
    suffices ∀ x, HasDerivAt (fun x => c⁻¹ * x) (c⁻¹ * 1) x by rwa [mul_one] at this
    exact fun _ ↦ HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (gaussianReal μ v).map e.symm = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v)
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs',
    gaussianReal_apply_eq_integral _ _ s']
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.mulLeft₀, Equiv.toFun_as_coe, Equiv.mulLeft₀_apply, Equiv.invFun_as_coe,
    Equiv.mulLeft₀_symm_apply, Homeomorph.toMeasurableEquiv_coe, Homeomorph.homeomorph_mk_coe_symm,
    Equiv.coe_fn_symm_mk, gaussianPDFReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv, inv_mul_cancel₀]
  rwa [ne_eq, abs_eq_zero]

lemma gaussianReal_map_mul_const (c : ℝ) :
    (gaussianReal μ v).map (· * c) = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  simp_rw [mul_comm _ c]
  exact gaussianReal_map_const_mul c

variable {Ω : Type} [MeasureSpace Ω]

lemma gaussianReal_add_const {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v) (y : ℝ) :
    Measure.map (fun ω ↦ X ω + y) ℙ = gaussianReal (μ + y) v := by
  have hXm : AEMeasurable X := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  change Measure.map ((fun ω ↦ ω + y) ∘ X) ℙ = gaussianReal (μ + y) v
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_id'.add_const _).aemeasurable hXm, hX,
    gaussianReal_map_add_const y]

lemma gaussianReal_const_add {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v) (y : ℝ) :
    Measure.map (fun ω ↦ y + X ω) ℙ = gaussianReal (μ + y) v := by
  simp_rw [add_comm y]
  exact gaussianReal_add_const hX y

lemma gaussianReal_const_mul {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v) (c : ℝ) :
    Measure.map (fun ω ↦ c * X ω) ℙ = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  have hXm : AEMeasurable X := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  change Measure.map ((fun ω ↦ c * ω) ∘ X) ℙ = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v)
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_id'.const_mul c).aemeasurable hXm, hX]
  exact gaussianReal_map_const_mul c

lemma gaussianReal_mul_const {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v) (c : ℝ) :
    Measure.map (fun ω ↦ X ω * c) ℙ = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  simp_rw [mul_comm _ c]
  exact gaussianReal_const_mul hX c

end Transformations

end GaussianReal

end ProbabilityTheory
