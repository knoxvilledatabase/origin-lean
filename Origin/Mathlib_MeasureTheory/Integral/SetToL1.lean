/-
Extracted from MeasureTheory/Integral/SetToL1.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Extension of a linear function from indicators to L1

Given `T : Set α → E →L[ℝ] F` with `DominatedFinMeasAdditive μ T C`, we construct an extension
of `T` to integrable simple functions, which are finite sums of indicators of measurable sets
with finite measure, then to integrable functions, which are limits of integrable simple functions.

The main result is a continuous linear map `(α →₁[μ] E) →L[ℝ] F`.
This extension process is used to define the Bochner integral
in the `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` file
and the conditional expectation of an integrable function
in `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondexpL1.lean`.

## Main definitions

- `setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α →₁[μ] E) →L[ℝ] F`: the extension of `T`
  from indicators to L1.
- `setToFun μ T (hT : DominatedFinMeasAdditive μ T C) (f : α → E) : F`: a version of the
  extension which applies to functions (with value 0 if the function is not integrable).

## Properties

For most properties of `setToFun`, we provide two lemmas. One version uses hypotheses valid on
all sets, like `T = T'`, and a second version which uses a primed name uses hypotheses on
measurable sets with finite measure, like `∀ s, MeasurableSet s → μ s < ∞ → T s = T' s`.

The lemmas listed here don't show all hypotheses. Refer to the actual lemmas for details.

Linearity:
- `setToFun_zero_left : setToFun μ 0 hT f = 0`
- `setToFun_add_left : setToFun μ (T + T') _ f = setToFun μ T hT f + setToFun μ T' hT' f`
- `setToFun_smul_left : setToFun μ (fun s ↦ c • (T s)) (hT.smul c) f = c • setToFun μ T hT f`
- `setToFun_zero : setToFun μ T hT (0 : α → E) = 0`
- `setToFun_neg : setToFun μ T hT (-f) = - setToFun μ T hT f`

If `f` and `g` are integrable:
- `setToFun_add : setToFun μ T hT (f + g) = setToFun μ T hT f + setToFun μ T hT g`
- `setToFun_sub : setToFun μ T hT (f - g) = setToFun μ T hT f - setToFun μ T hT g`

If `T` satisfies `∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x`:
- `setToFun_smul : setToFun μ T hT (c • f) = c • setToFun μ T hT f`

Other:
- `setToFun_congr_ae (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g`
- `setToFun_measure_zero (h : μ = 0) : setToFun μ T hT f = 0`

If the space is also an ordered additive group with an order closed topology and `T` is such that
`0 ≤ T s x` for `0 ≤ x`, we also prove order-related properties:
- `setToFun_mono_left (h : ∀ s x, T s x ≤ T' s x) : setToFun μ T hT f ≤ setToFun μ T' hT' f`
- `setToFun_nonneg (hf : 0 ≤ᵐ[μ] f) : 0 ≤ setToFun μ T hT f`
- `setToFun_mono (hfg : f ≤ᵐ[μ] g) : setToFun μ T hT f ≤ setToFun μ T hT g`
-/

noncomputable section

open scoped Topology NNReal

open Set Filter TopologicalSpace ENNReal

namespace MeasureTheory

variable {α E F F' G 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] {m : MeasurableSpace α} {μ : Measure α}

namespace L1

open AEEqFun Lp.simpleFunc Lp

namespace SimpleFunc

theorem norm_eq_sum_mul (f : α →₁ₛ[μ] G) :
    ‖f‖ = ∑ x ∈ (toSimpleFunc f).range, μ.real (toSimpleFunc f ⁻¹' {x}) * ‖x‖ := by
  rw [norm_toSimpleFunc, eLpNorm_one_eq_lintegral_enorm]
  have h_eq := SimpleFunc.map_apply (‖·‖ₑ) (toSimpleFunc f)
  simp_rw [← h_eq, measureReal_def]
  rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.map_lintegral, ENNReal.toReal_sum]
  · congr
    ext1 x
    rw [ENNReal.toReal_mul, mul_comm, ← ofReal_norm_eq_enorm,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  · intro x _
    by_cases hx0 : x = 0
    · rw [hx0]; simp
    · finiteness [SimpleFunc.measure_preimage_lt_top_of_integrable _ (SimpleFunc.integrable f) hx0]

section SetToL1S

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

attribute [local instance] Lp.simpleFunc.module

attribute [local instance] Lp.simpleFunc.normedSpace

def setToL1S (T : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) : F :=
  (toSimpleFunc f).setToSimpleFunc T
