/-
Extracted from MeasureTheory/Function/ConvergenceInDistribution.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Convergence in distribution

We introduce a definition of convergence in distribution of random variables: this is the
weak convergence of the laws of the random variables. In Mathlib terms this is a `Tendsto` in the
`ProbabilityMeasure` type.

We also state results relating convergence in probability (`TendstoInMeasure`)
and convergence in distribution.

## Main definitions

* `TendstoInDistribution X l Z μ`: the sequence of random variables `X n` converges in
  distribution to the random variable `Z` along the filter `l` with respect to the probability
  measure `μ`.

## Main statements

* `TendstoInDistribution.continuous_comp`: **Continuous mapping theorem**.
  If `X n` tends to `Z` in distribution and `g` is continuous, then `g ∘ X n` tends to `g ∘ Z`
  in distribution.
* `tendstoInDistribution_of_tendstoInMeasure_sub`: the main technical tool for the next results.
  Let `X, Y` be two sequences of measurable functions such that `X n` converges in distribution
  to `Z`, and `Y n - X n` converges in probability to `0`.
  Then `Y n` converges in distribution to `Z`.
* `TendstoInMeasure.tendstoInDistribution`: convergence in probability implies convergence in
  distribution.
* `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`: **Slutsky's theorem**.
  If `X n` converges in distribution to `Z`, and `Y n` converges in probability to a constant `c`,
  then the pair `(X n, Y n)` converges in distribution to `(Z, c)`.

-/

open Filter ProbabilityTheory

open scoped Topology

namespace MeasureTheory

variable {ι E Ω' Ω'' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {m'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
  {mE : MeasurableSpace E} {X Y : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι}

section TendstoInDistribution

variable [TopologicalSpace E]

structure TendstoInDistribution [OpensMeasurableSpace E] (X : (i : ι) → Ω i → E) (l : Filter ι)
    (Z : Ω' → E) (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (μ' : Measure Ω' := by volume_tac) [IsProbabilityMeasure μ'] : Prop where
  forall_aemeasurable : ∀ i, AEMeasurable (X i) (μ i)
  aemeasurable_limit : AEMeasurable Z μ' := by fun_prop
  tendsto : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (forall_aemeasurable n)⟩) l
      (𝓝 ⟨μ'.map Z, Measure.isProbabilityMeasure_map aemeasurable_limit⟩)

lemma tendstoInDistribution_const [OpensMeasurableSpace E] (hZ : AEMeasurable Z μ') :
    TendstoInDistribution (fun _ ↦ Z) l Z (fun _ ↦ μ') μ' where
  forall_aemeasurable := fun _ ↦ by fun_prop
  tendsto := tendsto_const_nhds

lemma tendstoInDistribution_of_identDistrib [OpensMeasurableSpace E] (i : ι)
    (hX : ∀ j, IdentDistrib (X i) (X j) (μ i) (μ j)) (hZ : IdentDistrib (X i) Z (μ i) μ') :
    TendstoInDistribution X l Z μ μ' where
  forall_aemeasurable j := (hX j).aemeasurable_snd
  aemeasurable_limit := hZ.aemeasurable_snd
  tendsto := by
    convert tendsto_const_nhds with j
    exact (hX j).map_eq.symm.trans hZ.map_eq
