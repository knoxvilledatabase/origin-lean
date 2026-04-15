/-
Extracted from Probability/Distributions/Gaussian/Basic.lean
Genuine: 6 of 10 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Gaussian distributions in Banach spaces

We introduce a predicate `IsGaussian` for measures on a Banach space `E` such that the map by
any continuous linear form is a Gaussian measure on `ℝ`.

For Gaussian distributions in `ℝ`, see the file
`Mathlib/Probability/Distributions/Gaussian/Real.lean`.

## Main definitions

* `IsGaussian`: a measure `μ` is Gaussian if its map by every continuous linear form
  `L : Dual ℝ E` is a real Gaussian measure.
  That is, `μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal`.

## Main statements

* `isGaussian_iff_charFunDual_eq`: a finite measure `μ` is Gaussian if and only if
  its characteristic function has value `exp (μ[L] * I - Var[L; μ] / 2)` for every
  continuous linear form `L : Dual ℝ E`.

## References

* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

-/

open MeasureTheory Complex

open scoped ENNReal NNReal

namespace ProbabilityTheory

class IsGaussian {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {mE : MeasurableSpace E} (μ : Measure E) : Prop where
  map_eq_gaussianReal (L : StrongDual ℝ E) : μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal

-- INSTANCE (free from Core): IsGaussian.toIsProbabilityMeasure

-- INSTANCE (free from Core): isGaussian_gaussianReal

lemma IsGaussian.eq_gaussianReal (μ : Measure ℝ) (h : IsGaussian μ) :
    μ = gaussianReal μ[id] Var[id; μ].toNNReal := calc
  μ = μ.map (ContinuousLinearMap.id ℝ ℝ) := by simp
  _ = gaussianReal μ[id] Var[id; μ].toNNReal := by rw [h.map_eq_gaussianReal]; simp

lemma isGaussian_of_isGaussian_map {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    (h : ∀ L : E →L[ℝ] ℝ, IsGaussian (μ.map L)) : IsGaussian μ := by
  refine ⟨fun L ↦ ?_⟩
  rw [(h L).eq_gaussianReal, integral_map, variance_map]
  · simp
  all_goals fun_prop

lemma isGaussian_map_of_measurable {E F : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} [TopologicalSpace F] [AddCommMonoid F]
    [Module ℝ F] {mF : MeasurableSpace F} [OpensMeasurableSpace F] {μ : Measure E}
    {L : E →L[ℝ] F} [IsGaussian μ] (hL : Measurable L) : IsGaussian (μ.map L) := by
  refine isGaussian_of_map_eq_gaussianReal fun L' ↦ ⟨μ[L' ∘L L], Var[L' ∘L L; μ].toNNReal, ?_⟩
  rw [Measure.map_map (by fun_prop) hL, ← ContinuousLinearMap.coe_comp',
    IsGaussian.map_eq_gaussianReal]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} [IsGaussian μ]

-- INSTANCE (free from Core): {x

omit [IsGaussian μ] in

lemma IsGaussian.of_subsingleton [Subsingleton E] [IsProbabilityMeasure μ] :
    IsGaussian μ := by
  convert instIsGaussianDirac (x := (0 : E))
  ext s -
  apply Subsingleton.set_cases (p := fun s ↦ μ s = _)
  all_goals simp

lemma IsGaussian.memLp_dual (μ : Measure E) [IsGaussian μ] (L : StrongDual ℝ E)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp L p μ := by
  suffices MemLp (id ∘ L) p μ from this
  rw [← memLp_map_measure_iff (by fun_prop) (by fun_prop), IsGaussian.map_eq_gaussianReal L]
  convert memLp_id_gaussianReal p.toNNReal
  simp [hp]
