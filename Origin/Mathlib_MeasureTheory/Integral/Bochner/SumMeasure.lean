/-
Extracted from MeasureTheory/Integral/Bochner/SumMeasure.lean
Genuine: 11 of 12 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Integral with respect to a sum of measures

In this file we prove that a function `f` is integrable with respect to a countable sum of measures
`Measure.sum μ` if and only if `f` is integrable with respect to each `μ i` and the sequence
`fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable. We then show that under this integrability condition,
`∫ x, f x ∂Measure.sum μ = ∑' i, ∫ f x ∂μ i`.

We specialize these results to the case where each measure is a Dirac mass,
i.e. `μ i = (c i) • .dirac (x i)`.

Finally we compute integrals over countable and finite spaces or sets.

## Main statements

* `integrable_sum_measure_iff`: A function `f` is integrable with respect to a countable sum
  of measures `Measure.sum μ` if and only if `f` is integrable with respect to each `μ i` and the
  sequence `fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable.
* `integrable_sum_dirac_iff`: A function `f` is integrable with respect to a countable sum
  of Dirac masses `Measure.sum (fun i ↦ (c i) • Measure.dirac (x i))` if and only if
  the sequence `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable.
* `hasSum_integral_measure`: If `f` is integrable with respect to `Measure.sum μ`,
  then the sequence `fun i ↦ ∫ x, f x ∂μ i` is summable and its sum is `∫ x, f x ∂Measure.sum μ`.
* `integral_sum_dirac_eq_tsum`: If the sequence `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable,
  then `∑' i, (c i).toReal • f (x i) = ∫ x, f x, ∂Measure.sum (fun i ↦ (c i) • .dirac (x i))`.

## Tags

sum of measures, integral, Dirac mass
-/

open Filter Set

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {ι X E : Type*} [Countable ι] {mX : MeasurableSpace X} [NormedAddCommGroup E]
  {μ : ι → Measure X} {f : X → E}

section Integrable

lemma integrable_sum_measure
    (hf : ∀ i, Integrable f (μ i)) (h : Summable (fun i ↦ ∫ x, ‖f x‖ ∂μ i)) :
    Integrable f (Measure.sum μ) := by
  refine ⟨aestronglyMeasurable_sum_measure_iff.mpr fun i ↦ (hf i).aestronglyMeasurable, ?_⟩
  · rw [HasFiniteIntegral, lintegral_sum_measure]
    convert h.tsum_ofReal_lt_top with i
    rw [ofReal_integral_eq_lintegral_ofReal (hf i).norm]
    · simp_rw [ofReal_norm_eq_enorm]
    · exact ae_of_all _ fun _ ↦ by positivity

omit [Countable ι] in

lemma Integrable.summable_integral (hf : Integrable f (Measure.sum μ)) :
    Summable (fun i ↦ ∫ x, ‖f x‖ ∂μ i) := by
  convert ENNReal.summable_toReal (f := fun i ↦ ∫⁻ x, ‖f x‖ₑ ∂μ i) ?_ with i
  · rw [← integral_toReal ?_ (by simp)]
    · simp
    · exact (hf.aestronglyMeasurable.mono_measure (Measure.le_sum _ i)).enorm
  rw [← lintegral_sum_measure]
  exact hf.2.ne

lemma integrable_sum_measure_iff :
    Integrable f (Measure.sum μ) ↔
      (∀ i, Integrable f (μ i)) ∧ Summable (fun i ↦ ∫ x, ‖f x‖ ∂μ i) where
  mp h := ⟨fun i ↦ h.mono_measure (Measure.le_sum _ i), h.summable_integral⟩
  mpr h := integrable_sum_measure h.1 h.2

section Dirac

variable [MeasurableSingletonClass X] {x : ι → X} {c : ι → ℝ≥0∞}

lemma integrable_sum_dirac (hc : ∀ i, c i ≠ ∞) (h : Summable (fun i ↦ (c i).toReal * ‖f (x i)‖)) :
    Integrable f (Measure.sum (fun i ↦ (c i) • .dirac (x i))) :=
  integrable_sum_measure (fun i ↦ (integrable_dirac (by simp)).smul_measure (hc i))
    (by simpa using h)

omit [Countable ι] in

lemma Integrable.summable_of_dirac
    (hf : Integrable f (Measure.sum (fun i ↦ (c i) • .dirac (x i)))) :
    Summable (fun i ↦ (c i).toReal * ‖f (x i)‖) := by
  simpa using hf.summable_integral

end Dirac

end Integrable

section Integral

variable [NormedSpace ℝ E]

omit [Countable ι] in

theorem hasSum_integral_measure (hf : Integrable f (Measure.sum μ)) :
    HasSum (fun i ↦ ∫ x, f x ∂μ i) (∫ x, f x ∂Measure.sum μ) := by
  have hfi : ∀ i, Integrable f (μ i) := fun i ↦ hf.mono_measure (Measure.le_sum _ _)
  simp only [HasSum, ← integral_finset_sum_measure fun i _ ↦ hfi i]
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr fun ε ε0 ↦ ?_
  lift ε to ℝ≥0 using ε0.le
  have hf_lt : (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < ∞ := hf.2
  have hmem : ∀ᶠ y in 𝓝 (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ), (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < y + ε := by
    refine tendsto_id.add tendsto_const_nhds (lt_mem_nhds (α := ℝ≥0∞) <| ENNReal.lt_add_right ?_ ?_)
    exacts [hf_lt.ne, ENNReal.coe_ne_zero.2 (NNReal.coe_ne_zero.1 ε0.ne')]
  refine ((hasSum_lintegral_measure (fun x ↦ ‖f x‖ₑ) μ).eventually hmem).mono fun s hs ↦ ?_
  obtain ⟨ν, hν⟩ : ∃ ν, (∑ i ∈ s, μ i) + ν = Measure.sum μ := by
    refine ⟨Measure.sum fun i : ↥(sᶜ : Set ι) ↦ μ i, ?_⟩
    simpa only [← Measure.sum_coe_finset] using Measure.sum_add_sum_compl (s : Set ι) μ
  rw [Metric.mem_ball, ← coe_nndist, NNReal.coe_lt_coe, ← ENNReal.coe_lt_coe, ← hν]
  rw [← hν, integrable_add_measure] at hf
  refine (nndist_integral_add_measure_le_lintegral hf.1 hf.2).trans_lt ?_
  rw [← hν, lintegral_add_measure, lintegral_finset_sum_measure] at hs
  exact lt_of_add_lt_add_left hs

omit [Countable ι] in

theorem integral_sum_measure (hf : Integrable f (Measure.sum μ)) :
    ∫ x, f x ∂Measure.sum μ = ∑' i, ∫ x, f x ∂μ i :=
  (hasSum_integral_measure hf).tsum_eq.symm

section Dirac

variable [MeasurableSingletonClass X] {x : ι → X} {c : ι → ℝ≥0∞}

lemma integral_sum_dirac [FiniteDimensional ℝ E] (hc : ∀ i, c i ≠ ∞) :
    ∫ x, f x ∂Measure.sum (fun i ↦ (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (x i) := by
  by_cases hf : Integrable f (.sum (fun i ↦ (c i) • .dirac (x i)))
  · rw [integral_sum_measure hf]
    congr with i
    rw [integral_smul_measure, integral_dirac]
  · rw [integral_undef hf, tsum_eq_zero_of_not_summable]
    apply mt Summable.norm
    convert mt (integrable_sum_dirac hc) hf
    simp [norm_smul]

lemma hasSum_integral_sum_dirac [CompleteSpace E] (hc : ∀ i, c i ≠ ∞)
    (hf : Summable (fun i ↦ (c i).toReal * ‖f (x i)‖)) :
    HasSum (fun i ↦ (c i).toReal • f (x i))
      (∫ x, f x ∂Measure.sum (fun i ↦ (c i) • .dirac (x i))) := by
  simpa using hasSum_integral_measure (integrable_sum_dirac hc hf)

lemma integral_sum_dirac_eq_tsum [CompleteSpace E] (hc : ∀ i, c i ≠ ∞)
    (hf : Summable (fun i ↦ (c i).toReal * ‖f (x i)‖)) :
    ∫ x, f x ∂Measure.sum (fun i ↦ (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (x i) :=
  (hasSum_integral_sum_dirac hc hf).tsum_eq.symm

end Dirac

section DiscreteSpace

variable [CompleteSpace E] [MeasurableSingletonClass X] {μ : Measure X}

theorem integral_countable [Countable X] (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' x, μ.real {x} • f x := by
  rw [← Measure.sum_smul_dirac μ] at hf
  rw [← Measure.sum_smul_dirac μ, integral_sum_measure hf]
  congr 1 with a : 1
  rw [integral_smul_measure, integral_dirac, Measure.sum_smul_dirac, measureReal_def]
