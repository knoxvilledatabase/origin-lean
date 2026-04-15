/-
Extracted from MeasureTheory/Measure/DiracProba.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dirac deltas as probability measures and embedding of a space into probability measures on it

## Main definitions
* `diracProba`: The Dirac delta mass at a point as a probability measure.

## Main results
* `isEmbedding_diracProba`: If `X` is a completely regular T0 space with its Borel sigma algebra,
  then the mapping that takes a point `x : X` to the delta-measure `diracProba x` is an embedding
  `X ↪ ProbabilityMeasure X`.

## Tags
probability measure, Dirac delta, embedding
-/

open Topology Metric Filter Set ENNReal NNReal BoundedContinuousFunction

open scoped Topology ENNReal NNReal BoundedContinuousFunction

lemma CompletelyRegularSpace.exists_BCNN {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
    {K : Set X} (K_closed : IsClosed K) {x : X} (x_notin_K : x ∉ K) :
    ∃ (f : X →ᵇ ℝ≥0), f x = 1 ∧ (∀ y ∈ K, f y = 0) := by
  obtain ⟨g, g_cont, gx_zero, g_one_on_K⟩ :=
    CompletelyRegularSpace.completely_regular x K K_closed x_notin_K
  have g_bdd : ∀ x y, dist (Real.toNNReal (g x)) (Real.toNNReal (g y)) ≤ 1 := by
    refine fun x y ↦ ((Real.lipschitzWith_toNNReal).dist_le_mul (g x) (g y)).trans ?_
    simpa using Real.dist_le_of_mem_Icc_01 (g x).prop (g y).prop
  set g' := BoundedContinuousFunction.mkOfBound
      ⟨fun x ↦ Real.toNNReal (g x), continuous_real_toNNReal.comp g_cont.subtype_val⟩ 1 g_bdd
  set f := 1 - g'
  refine ⟨f, by simp [f, g', gx_zero], fun y y_in_K ↦ by simp [f, g', g_one_on_K y_in_K, tsub_self]⟩

namespace MeasureTheory

section embed_to_probabilityMeasure

variable {X : Type*} [MeasurableSpace X]

noncomputable def diracProba (x : X) : ProbabilityMeasure X :=
  ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

set_option backward.isDefEq.respectTransparency false in

lemma injective_diracProba {X : Type*} [MeasurableSpace X] [MeasurableSpace.SeparatesPoints X] :
    Function.Injective (fun (x : X) ↦ diracProba x) := by
  intro x y x_eq_y
  rw [← dirac_eq_dirac_iff]
  rwa [Subtype.ext_iff] at x_eq_y
