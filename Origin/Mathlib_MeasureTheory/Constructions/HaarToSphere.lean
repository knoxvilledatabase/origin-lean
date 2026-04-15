/-
Extracted from MeasureTheory/Constructions/HaarToSphere.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Generalized polar coordinate change

Consider an `n`-dimensional normed space `E` and an additive Haar measure `μ` on `E`.
Then `μ.toSphere` is the measure on the unit sphere
such that `μ.toSphere s` equals `n • μ (Set.Ioo 0 1 • s)`.

If `n ≠ 0`, then `μ` can be represented (up to `homeomorphUnitSphereProd`)
as the product of `μ.toSphere`
and the Lebesgue measure on `(0, +∞)` taken with density `fun r ↦ r ^ n`.

One can think about this fact as a version of polar coordinate change formula
for a general nontrivial normed space.

In this file we provide a way to rewrite integrals and integrability
of functions that depend on the norm only in terms of integral over `(0, +∞)`.
We also provide a positive lower estimate on the `(Measure.toSphere μ)`-measure
of a ball of radius `ε > 0` on the unit sphere.
-/

open Set Function Metric MeasurableSpace intervalIntegral

open scoped Pointwise ENNReal NNReal

local notation "dim" => Module.finrank ℝ

noncomputable section

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

namespace Measure

def toSphere (μ : Measure E) : Measure (sphere (0 : E) 1) :=
  dim E • ((μ.comap (Subtype.val ∘ (homeomorphUnitSphereProd E).symm)).restrict
    (univ ×ˢ Iio ⟨1, mem_Ioi.2 one_pos⟩)).fst

variable (μ : Measure E)

theorem toSphere_apply_aux (s : Set (sphere (0 : E) 1)) (r : Ioi (0 : ℝ)) :
    μ ((↑) '' (homeomorphUnitSphereProd E ⁻¹' s ×ˢ Iio r)) = μ (Ioo (0 : ℝ) r • ((↑) '' s)) := by
  rw [← image2_smul, image2_image_right, ← Homeomorph.image_symm, image_image,
    ← image_subtype_val_Ioi_Iio, image2_image_left, image2_swap, ← image_prod]
  rfl

variable [BorelSpace E]

theorem toSphere_apply' {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    μ.toSphere s = dim E * μ (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  rw [toSphere, smul_apply, fst_apply hs, restrict_apply (measurable_fst hs),
    ((MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).comp
      (Homeomorph.measurableEmbedding _)).comap_apply,
    image_comp, Homeomorph.image_symm, univ_prod, ← Set.prod_eq, nsmul_eq_mul, toSphere_apply_aux]

theorem toSphere_apply_univ' : μ.toSphere univ = dim E * μ (ball 0 1 \ {0}) := by
  rw [μ.toSphere_apply' .univ, image_univ, Subtype.range_coe, Ioo_smul_sphere_zero] <;> simp

-- INSTANCE (free from Core): toSphere.instIsOpenPosMeasure

variable [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]
