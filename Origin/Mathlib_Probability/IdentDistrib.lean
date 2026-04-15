/-
Extracted from Probability/IdentDistrib.lean
Genuine: 20 of 30 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Identically distributed random variables

Two random variables defined on two (possibly different) probability spaces but taking value in
the same space are *identically distributed* if their distributions (i.e., the image probability
measures on the target space) coincide. We define this concept and establish its basic properties
in this file.

## Main definitions and results

* `IdentDistrib f g μ ν` registers that the image of `μ` under `f` coincides with the image of `ν`
  under `g` (and that `f` and `g` are almost everywhere measurable, as otherwise the image measures
  don't make sense). The measures can be kept implicit as in `IdentDistrib f g` if the spaces
  are registered as measure spaces.
* `IdentDistrib.comp`: being identically distributed is stable under composition with measurable
  maps.

There are two main kinds of lemmas, under the assumption that `f` and `g` are identically
distributed: lemmas saying that two quantities computed for `f` and `g` are the same, and lemmas
saying that if `f` has some property then `g` also has it. The first kind is registered as
`IdentDistrib.foo_fst`, the second one as `IdentDistrib.foo_snd` (in the latter case, to deduce
a property of `f` from one of `g`, use `h.symm.foo_snd` where `h : IdentDistrib f g μ ν`). For
instance:

* `IdentDistrib.measure_mem_eq`: if `f` and `g` are identically distributed, then the probabilities
  that they belong to a given measurable set are the same.
* `IdentDistrib.integral_eq`: if `f` and `g` are identically distributed, then their integrals
  are the same.
* `IdentDistrib.variance_eq`: if `f` and `g` are identically distributed, then their variances
  are the same.

* `IdentDistrib.aestronglyMeasurable_snd`: if `f` and `g` are identically distributed and `f`
  is almost everywhere strongly measurable, then so is `g`.
* `IdentDistrib.memLp_snd`: if `f` and `g` are identically distributed and `f`
  belongs to `ℒp`, then so does `g`.

We also register several dot notation shortcuts for convenience.
For instance, if `h : IdentDistrib f g μ ν`, then `h.sq` states that `f^2` and `g^2` are
identically distributed, and `h.norm` states that `‖f‖` and `‖g‖` are identically distributed, and
so on.
-/

open MeasureTheory Filter Finset

noncomputable section

open scoped Topology MeasureTheory ENNReal NNReal

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace ProbabilityTheory

structure IdentDistrib (f : α → γ) (g : β → γ)
    (μ : Measure α := by volume_tac)
    (ν : Measure β := by volume_tac) : Prop where
  aemeasurable_fst : AEMeasurable f μ
  aemeasurable_snd : AEMeasurable g ν
  map_eq : Measure.map f μ = Measure.map g ν

namespace IdentDistrib

open TopologicalSpace

variable {μ : Measure α} {ν : Measure β} {f : α → γ} {g : β → γ}

protected theorem trans {ρ : Measure δ} {h : δ → γ} (h₁ : IdentDistrib f g μ ν)
    (h₂ : IdentDistrib g h ν ρ) : IdentDistrib f h μ ρ :=
  { aemeasurable_fst := h₁.aemeasurable_fst
    aemeasurable_snd := h₂.aemeasurable_snd
    map_eq := h₁.map_eq.trans h₂.map_eq }

protected theorem comp_of_aemeasurable {u : γ → δ} (h : IdentDistrib f g μ ν)
    (hu : AEMeasurable u (Measure.map f μ)) : IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  { aemeasurable_fst := hu.comp_aemeasurable h.aemeasurable_fst
    aemeasurable_snd := by rw [h.map_eq] at hu; exact hu.comp_aemeasurable h.aemeasurable_snd
    map_eq := by
      rw [← AEMeasurable.map_map_of_aemeasurable hu h.aemeasurable_fst, ←
        AEMeasurable.map_map_of_aemeasurable _ h.aemeasurable_snd, h.map_eq]
      rwa [← h.map_eq] }

protected theorem of_ae_eq {g : α → γ} (hf : AEMeasurable f μ) (heq : f =ᵐ[μ] g) :
    IdentDistrib f g μ μ :=
  { aemeasurable_fst := hf
    aemeasurable_snd := hf.congr heq
    map_eq := Measure.map_congr heq }

lemma _root_.MeasureTheory.AEMeasurable.identDistrib_mk
    (hf : AEMeasurable f μ) : IdentDistrib f (hf.mk f) μ μ :=
  IdentDistrib.of_ae_eq hf hf.ae_eq_mk

lemma _root_.MeasureTheory.AEStronglyMeasurable.identDistrib_mk
    [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (hf : AEStronglyMeasurable f μ) : IdentDistrib f (hf.mk f) μ μ :=
  IdentDistrib.of_ae_eq hf.aemeasurable hf.ae_eq_mk

theorem measure_mem_eq (h : IdentDistrib f g μ ν) {s : Set γ} (hs : MeasurableSet s) :
    μ (f ⁻¹' s) = ν (g ⁻¹' s) := by
  rw [← Measure.map_apply_of_aemeasurable h.aemeasurable_fst hs, ←
    Measure.map_apply_of_aemeasurable h.aemeasurable_snd hs, h.map_eq]

alias measure_preimage_eq := measure_mem_eq

theorem ae_snd (h : IdentDistrib f g μ ν) {p : γ → Prop} (pmeas : MeasurableSet {x | p x})
    (hp : ∀ᵐ x ∂μ, p (f x)) : ∀ᵐ x ∂ν, p (g x) := by
  apply (ae_map_iff h.aemeasurable_snd pmeas).1
  rw [← h.map_eq]
  exact (ae_map_iff h.aemeasurable_fst pmeas).2 hp

theorem _root_.ProbabilityTheory.HasLaw.identDistrib {κ : Measure γ} (h₀ : HasLaw f κ μ)
    (h₁ : HasLaw g κ ν) : IdentDistrib f g μ ν :=
  ⟨h₀.aemeasurable, h₁.aemeasurable, by simp [h₀.map_eq, h₁.map_eq]⟩

theorem hasLaw {κ : Measure γ} (h₀ : IdentDistrib f g μ ν) (h₁ : HasLaw f κ μ) : HasLaw g κ ν :=
  ⟨h₀.aemeasurable_snd, by simp [h₀.map_eq, ← h₁.map_eq]⟩

theorem aestronglyMeasurable_snd [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable g ν := by
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨h.aemeasurable_snd, ?_⟩
  rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
  refine ⟨closure t, t_sep.closure, ?_⟩
  apply h.ae_mem_snd isClosed_closure.measurableSet
  filter_upwards [ht] with x hx using subset_closure hx

theorem aestronglyMeasurable_iff [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) : AEStronglyMeasurable f μ ↔ AEStronglyMeasurable g ν :=
  ⟨fun hf => h.aestronglyMeasurable_snd hf, fun hg => h.symm.aestronglyMeasurable_snd hg⟩

theorem essSup_eq [ConditionallyCompleteLinearOrder γ] [TopologicalSpace γ] [OpensMeasurableSpace γ]
    [OrderClosedTopology γ] (h : IdentDistrib f g μ ν) : essSup f μ = essSup g ν := by
  have I : ∀ a, μ {x : α | a < f x} = ν {x : β | a < g x} := fun a =>
    h.measure_mem_eq measurableSet_Ioi
  simp_rw [essSup_eq_sInf, I]

theorem lintegral_eq {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (h : IdentDistrib f g μ ν) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂ν := by
  change ∫⁻ x, id (f x) ∂μ = ∫⁻ x, id (g x) ∂ν
  rw [← lintegral_map' aemeasurable_id h.aemeasurable_fst, ←
    lintegral_map' aemeasurable_id h.aemeasurable_snd, h.map_eq]

theorem integral_eq [NormedAddCommGroup γ] [NormedSpace ℝ γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) : ∫ x, f x ∂μ = ∫ x, g x ∂ν := by
  by_cases hf : AEStronglyMeasurable f μ
  · have A : AEStronglyMeasurable id (Measure.map f μ) := by
      rw [aestronglyMeasurable_iff_aemeasurable_separable]
      rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
      refine ⟨aemeasurable_id, ⟨closure t, t_sep.closure, ?_⟩⟩
      rw [ae_map_iff h.aemeasurable_fst]
      · filter_upwards [ht] with x hx using subset_closure hx
      · exact isClosed_closure.measurableSet
    change ∫ x, id (f x) ∂μ = ∫ x, id (g x) ∂ν
    rw [← integral_map h.aemeasurable_fst A]
    rw [h.map_eq] at A
    rw [← integral_map h.aemeasurable_snd A, h.map_eq]
  · rw [integral_non_aestronglyMeasurable hf]
    rw [h.aestronglyMeasurable_iff] at hf
    rw [integral_non_aestronglyMeasurable hf]

theorem eLpNorm_eq [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν)
    (p : ℝ≥0∞) : eLpNorm f p μ = eLpNorm g p ν := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm, eLpNormEssSup, ENNReal.top_ne_zero, if_true,
      if_false]
    apply essSup_eq
    exact h.comp (measurable_coe_nnreal_ennreal.comp measurable_nnnorm)
  simp only [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm', one_div]
  congr 1
  apply lintegral_eq
  exact h.comp (Measurable.pow_const (measurable_coe_nnreal_ennreal.comp measurable_nnnorm)
    p.toReal)

theorem memLp_snd [NormedAddCommGroup γ] [BorelSpace γ] {p : ℝ≥0∞} (h : IdentDistrib f g μ ν)
    (hf : MemLp f p μ) : MemLp g p ν := by
  refine ⟨h.aestronglyMeasurable_snd hf.aestronglyMeasurable, ?_⟩
  rw [← h.eLpNorm_eq]
  exact hf.2

theorem memLp_iff [NormedAddCommGroup γ] [BorelSpace γ] {p : ℝ≥0∞} (h : IdentDistrib f g μ ν) :
    MemLp f p μ ↔ MemLp g p ν :=
  ⟨fun hf => h.memLp_snd hf, fun hg => h.symm.memLp_snd hg⟩

theorem integrable_snd [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν)
    (hf : Integrable f μ) : Integrable g ν := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact h.memLp_snd hf

theorem integrable_iff [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    Integrable f μ ↔ Integrable g ν :=
  ⟨fun hf => h.integrable_snd hf, fun hg => h.symm.integrable_snd hg⟩
