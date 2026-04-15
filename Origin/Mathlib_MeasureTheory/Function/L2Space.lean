/-
Extracted from MeasureTheory/Function/L2Space.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # `L^2` space

If `E` is an inner product space over `𝕜` (`ℝ` or `ℂ`), then `Lp E 2 μ`
(defined in `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
is also an inner product space, with inner product defined as `inner f g := ∫ a, ⟪f a, g a⟫ ∂μ`.

### Main results

* `mem_L1_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `fun x ↦ ⟪f x, g x⟫`
  belongs to `Lp 𝕜 1 μ`.
* `integrable_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product
  `fun x ↦ ⟪f x, g x⟫` is integrable.
* `L2.innerProductSpace` : `Lp E 2 μ` is an inner product space.
-/

noncomputable section

open TopologicalSpace MeasureTheory MeasureTheory.Lp Filter

open scoped NNReal ENNReal MeasureTheory InnerProductSpace

namespace MeasureTheory

variable {α F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F]

theorem MemLp.integrable_sq {f : α → ℝ} (h : MemLp f 2 μ) : Integrable (fun x => f x ^ 2) μ := by
  simpa [← memLp_one_iff_integrable] using h.norm_rpow two_ne_zero ENNReal.ofNat_ne_top

theorem memLp_two_iff_integrable_sq_norm {f : α → F} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => ‖f x‖ ^ 2) μ := by
  rw [← memLp_one_iff_integrable]
  convert (memLp_norm_rpow_iff hf two_ne_zero ENNReal.ofNat_ne_top).symm
  · simp
  · rw [div_eq_mul_inv, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

theorem memLp_two_iff_integrable_sq {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ := by
  convert memLp_two_iff_integrable_sq_norm hf using 3
  simp

end

section InnerProductSpace

variable {α : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}

variable {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem MemLp.const_inner (c : E) {f : α → E} (hf : MemLp f p μ) : MemLp (fun a => ⟪c, f a⟫) p μ :=
  hf.of_le_mul (AEStronglyMeasurable.inner aestronglyMeasurable_const hf.1)
    (Eventually.of_forall fun _ => norm_inner_le_norm _ _)

theorem MemLp.inner_const {f : α → E} (hf : MemLp f p μ) (c : E) : MemLp (fun a => ⟪f a, c⟫) p μ :=
  hf.of_le_mul (c := ‖c‖) (AEStronglyMeasurable.inner hf.1 aestronglyMeasurable_const)
    (Eventually.of_forall fun x => by rw [mul_comm]; exact norm_inner_le_norm _ _)

variable {f : α → E}
