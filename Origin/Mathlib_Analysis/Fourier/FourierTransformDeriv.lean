/-
Extracted from Analysis/Fourier/FourierTransformDeriv.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Derivatives of the Fourier transform

In this file we compute the Fréchet derivative of the Fourier transform of `f`, where `f` is a
function such that both `f` and `v ↦ ‖v‖ * ‖f v‖` are integrable. Here the Fourier transform is
understood as an operator `(V → E) → (W → E)`, where `V` and `W` are normed `ℝ`-vector spaces
and the Fourier transform is taken with respect to a continuous `ℝ`-bilinear
pairing `L : V × W → ℝ` and a given reference measure `μ`.

We also investigate higher derivatives: Assuming that `‖v‖^n * ‖f v‖` is integrable, we show
that the Fourier transform of `f` is `C^n`.

We also study in a parallel way the Fourier transform of the derivative, which is obtained by
tensoring the Fourier transform of the original function with the bilinear form. We also get
results for iterated derivatives.

A consequence of these results is that, if a function is smooth and all its derivatives are
integrable when multiplied by `‖v‖^k`, then the same goes for its Fourier transform, with
explicit bounds.

We give specialized versions of these results on inner product spaces (where `L` is the scalar
product) and on the real line, where we express the one-dimensional derivative in more concrete
terms, as the Fourier transform of `-2πI x * f x` (or `(-2πI x)^n * f x` for higher derivatives).

## Main definitions and results

We introduce two convenience definitions:

* `VectorFourier.fourierSMulRight L f`: given `f : V → E` and `L` a bilinear pairing
  between `V` and `W`, then this is the function `fun v ↦ -(2 * π * I) (L v ⬝) • f v`,
  from `V` to `Hom (W, E)`.
  This is essentially `ContinuousLinearMap.smulRight`, up to the factor `- 2πI` designed to make
  sure that the Fourier integral of `fourierSMulRight L f` is the derivative of the Fourier
  integral of `f`.
* `VectorFourier.fourierPowSMulRight` is the higher-order analogue for higher derivatives:
  `fourierPowSMulRight L f v n` is informally `(-(2 * π * I))^n (L v ⬝)^n • f v`, in
  the space of continuous multilinear maps `W [×n]→L[ℝ] E`.

With these definitions, the statements read as follows, first in a general context
(arbitrary `L` and `μ`):

* `VectorFourier.hasFDerivAt_fourierIntegral`: the Fourier integral of `f` is differentiable, with
    derivative the Fourier integral of `fourierSMulRight L f`.
* `VectorFourier.differentiable_fourierIntegral`: the Fourier integral of `f` is differentiable.
* `VectorFourier.fderiv_fourierIntegral`: formula for the derivative of the Fourier integral of `f`.
* `VectorFourier.fourierIntegral_fderiv`: formula for the Fourier integral of the derivative of `f`.
* `VectorFourier.hasFTaylorSeriesUpTo_fourierIntegral`: under suitable integrability conditions,
  the Fourier integral of `f` has an explicit Taylor series up to order `N`, given by the Fourier
  integrals of `fun v ↦ fourierPowSMulRight L f v n`.
* `VectorFourier.contDiff_fourierIntegral`: under suitable integrability conditions,
  the Fourier integral of `f` is `C^n`.
* `VectorFourier.iteratedFDeriv_fourierIntegral`: under suitable integrability conditions,
  explicit formula for the `n`-th derivative of the Fourier integral of `f`, as the Fourier
  integral of `fun v ↦ fourierPowSMulRight L f v n`.
* `VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le`: explicit bounds for the `n`-th
  derivative of the Fourier integral, multiplied by a power function, in terms of corresponding
  integrals for the original function.

These statements are then specialized to the case of the usual Fourier transform on
finite-dimensional inner product spaces with their canonical Lebesgue measure (covering in
particular the case of the real line), replacing the namespace `VectorFourier` by
the namespace `Real` in the above statements.

We also give specialized versions of the one-dimensional real derivative (and iterated derivative)
in `Real.deriv_fourierIntegral` and `Real.iteratedDeriv_fourierIntegral`.
-/

noncomputable section

open Real Complex MeasureTheory Filter TopologicalSpace

open scoped FourierTransform Topology ContDiff

-- INSTANCE (free from Core): 101]

namespace Real

lemma hasDerivAt_fourierChar (x : ℝ) : HasDerivAt (𝐞 · : ℝ → ℂ) (2 * π * I * 𝐞 x) x := by
  have h1 (y : ℝ) : 𝐞 y = fourier 1 (y : UnitAddCircle) := by
    rw [fourierChar_apply, fourier_coe_apply]
    push_cast
    ring_nf
  simpa only [h1, Int.cast_one, ofReal_one, div_one, mul_one] using hasDerivAt_fourier 1 1 x

lemma differentiable_fourierChar : Differentiable ℝ (𝐞 · : ℝ → ℂ) :=
  fun x ↦ (Real.hasDerivAt_fourierChar x).differentiableAt

lemma deriv_fourierChar (x : ℝ) : deriv (𝐞 · : ℝ → ℂ) x = 2 * π * I * 𝐞 x :=
  (Real.hasDerivAt_fourierChar x).deriv

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ)

set_option backward.isDefEq.respectTransparency false in

lemma hasFDerivAt_fourierChar_neg_bilinear_right (v : V) (w : W) :
    HasFDerivAt (fun w ↦ (𝐞 (-L v w) : ℂ))
      ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L v))) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert (hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg using 1
  ext y
  simp only [neg_mul, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Pi.smul_apply,
    Function.comp_apply, ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.toSpanSingleton_apply, real_smul, neg_inj]
  ring

lemma fderiv_fourierChar_neg_bilinear_right_apply (v : V) (w y : W) :
    fderiv ℝ (fun w ↦ (𝐞 (-L v w) : ℂ)) w y = -2 * π * I * L v y * 𝐞 (-L v w) := by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_right L v w).fderiv, neg_mul,
    ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Pi.smul_apply,
    Function.comp_apply, ofRealCLM_apply, smul_eq_mul, neg_inj]
  ring

lemma differentiable_fourierChar_neg_bilinear_right (v : V) :
    Differentiable ℝ (fun w ↦ (𝐞 (-L v w) : ℂ)) :=
  fun w ↦ (hasFDerivAt_fourierChar_neg_bilinear_right L v w).differentiableAt

lemma hasFDerivAt_fourierChar_neg_bilinear_left (v : V) (w : W) :
    HasFDerivAt (fun v ↦ (𝐞 (-L v w) : ℂ))
      ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L.flip w))) v :=
  hasFDerivAt_fourierChar_neg_bilinear_right L.flip w v

lemma fderiv_fourierChar_neg_bilinear_left_apply (v y : V) (w : W) :
    fderiv ℝ (fun v ↦ (𝐞 (-L v w) : ℂ)) v y = -2 * π * I * L y w * 𝐞 (-L v w) := by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_left L v w).fderiv, neg_mul,
    ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Pi.smul_apply,
    Function.comp_apply, ContinuousLinearMap.flip_apply, ofRealCLM_apply, smul_eq_mul, neg_inj]
  ring

lemma differentiable_fourierChar_neg_bilinear_left (w : W) :
    Differentiable ℝ (fun v ↦ (𝐞 (-L v w) : ℂ)) :=
  fun v ↦ (hasFDerivAt_fourierChar_neg_bilinear_left L v w).differentiableAt

end Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace VectorFourier

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E)

def fourierSMulRight (v : V) : (W →L[ℝ] E) := -(2 * π * I) • (L v).smulRight (f v)
