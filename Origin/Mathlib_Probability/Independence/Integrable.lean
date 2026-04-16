/-
Extracted from Probability/Independence/Integrable.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.Probability.Independence.Basic

noncomputable section

/-!
# Independence of functions implies that the measure is a probability measure

If a nonzero function belongs to `ℒ^p` (in particular if it is integrable) and is independent
of another function, then the space is a probability space.

-/

open Filter ProbabilityTheory

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {Ω E F: Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F]

lemma Memℒp.isProbabilityMeasure_of_indepFun
    (f : Ω → E) (g : Ω → F) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞)
    (hℒp : Memℒp f p μ) (h'f : ¬ (∀ᵐ ω ∂μ, f ω = 0)) (hindep : IndepFun f g μ) :
    IsProbabilityMeasure μ := by
  obtain ⟨c, c_pos, hc⟩ : ∃ (c : ℝ≥0), 0 < c ∧ 0 < μ {ω | c ≤ ‖f ω‖₊} := by
    contrapose! h'f
    have A (c : ℝ≥0) (hc : 0 < c) : ∀ᵐ ω ∂μ, ‖f ω‖₊ < c := by simpa [ae_iff] using h'f c hc
    obtain ⟨u, -, u_pos, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n)
      ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto (0 : ℝ≥0)
    filter_upwards [ae_all_iff.2 (fun n ↦ A (u n) (u_pos n))] with ω hω
    simpa using ge_of_tendsto' u_lim (fun i ↦ (hω i).le)
  have h'c : μ {ω | c ≤ ‖f ω‖₊} < ∞ := hℒp.meas_ge_lt_top hp hp' c_pos.ne'
  have := hindep.measure_inter_preimage_eq_mul {x | c ≤ ‖x‖₊} Set.univ
    (isClosed_le continuous_const continuous_nnnorm).measurableSet MeasurableSet.univ
  simp only [Set.preimage_setOf_eq, Set.preimage_univ, Set.inter_univ] at this
  exact ⟨(ENNReal.mul_eq_left hc.ne' h'c.ne).1 this.symm⟩

lemma Integrable.isProbabilityMeasure_of_indepFun (f : Ω → E) (g : Ω → F)
    (hf : Integrable f μ) (h'f : ¬ (∀ᵐ ω ∂μ, f ω = 0)) (hindep : IndepFun f g μ) :
    IsProbabilityMeasure μ :=
  Memℒp.isProbabilityMeasure_of_indepFun f g one_ne_zero ENNReal.one_ne_top
    (memℒp_one_iff_integrable.mpr hf) h'f hindep

end MeasureTheory
