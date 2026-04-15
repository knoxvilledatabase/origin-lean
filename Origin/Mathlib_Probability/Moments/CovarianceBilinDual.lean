/-
Extracted from Probability/Moments/CovarianceBilinDual.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Covariance in Banach spaces

We define the covariance of a finite measure in a Banach space `E`,
as a continuous bilinear form on `Dual ℝ E`.

## Main definitions

Let `μ` be a finite measure on a normed space `E` with the Borel σ-algebra. We then define

* `Dual.toLp`: the function `MemLp.toLp` as a continuous linear map from `Dual 𝕜 E` (for `RCLike 𝕜`)
  into the space `Lp 𝕜 p μ` for `p ≥ 1`. This needs a hypothesis `MemLp id p μ` (we set it to the
  junk value 0 if that's not the case).
* `covarianceBilinDual` : covariance of a measure `μ` with `∫ x, ‖x‖^2 ∂μ < ∞` on a Banach space,
  as a continuous bilinear form `Dual ℝ E →L[ℝ] Dual ℝ E →L[ℝ] ℝ`.
  If the second moment of `μ` is not finite, we set `covarianceBilinDual μ = 0`.

## Main statements

* `covarianceBilinDual_apply` : the covariance of `μ` on `L₁, L₂ : Dual ℝ E` is equal to
  `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ`.
* `covarianceBilinDual_same_eq_variance`: `covarianceBilinDual μ L L = Var[L; μ]`.

## Implementation notes

The hypothesis that `μ` has a second moment is written as `MemLp id 2 μ` in the code.

-/

open MeasureTheory ProbabilityTheory Complex NormedSpace

open scoped ENNReal NNReal Real Topology

variable {E : Type*} [NormedAddCommGroup E] {mE : MeasurableSpace E} {μ : Measure E} {p : ℝ≥0∞}

namespace StrongDual

section LinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

open Classical in

noncomputable

def toLpₗ (μ : Measure E) (p : ℝ≥0∞) :
    StrongDual 𝕜 E →ₗ[𝕜] Lp 𝕜 p μ :=
  if h_Lp : MemLp id p μ then
  { toFun := fun L ↦ MemLp.toLp L (h_Lp.continuousLinearMap_comp L)
    map_add' u v := by push_cast; rw [MemLp.toLp_add]
    map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl }
  else 0
