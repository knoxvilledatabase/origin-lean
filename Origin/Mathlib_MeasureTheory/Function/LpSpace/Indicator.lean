/-
Extracted from MeasureTheory/Function/LpSpace/Indicator.lean
Genuine: 15 of 19 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core

/-!
# Indicator of a set as an element of `Lp`

For a set `s` with `(hs : MeasurableSet s)` and `(hμs : μ s < ∞)`, we build
`indicatorConstLp p hs hμs c`, the element of `Lp` corresponding to `s.indicator (fun _ => c)`.

## Main definitions

* `MeasureTheory.indicatorConstLp`: Indicator of a set as an element of `Lp`.
* `MeasureTheory.Lp.const`: Constant function as an element of `Lp` for a finite measure.
-/

noncomputable section

open MeasureTheory Filter

open scoped NNReal ENNReal Topology symmDiff

variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} [NormedAddCommGroup E]

namespace MeasureTheory

-- DISSOLVED: exists_eLpNorm_indicator_le

section Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

theorem _root_.HasCompactSupport.memLp_of_bound {f : X → E} (hf : HasCompactSupport f)
    (h2f : AEStronglyMeasurable f μ) (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : MemLp f p μ := by
  have := memLp_top_of_bound h2f C hfC
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_notMem_tsupport) (hf.measure_lt_top.ne) le_top

theorem _root_.Continuous.memLp_of_hasCompactSupport [OpensMeasurableSpace X]
    {f : X → E} (hf : Continuous f) (h'f : HasCompactSupport f) : MemLp f p μ := by
  have := hf.memLp_top_of_hasCompactSupport h'f μ
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_notMem_tsupport) (h'f.measure_lt_top.ne) le_top

end Topology

section IndicatorConstLp

open Set Function

variable {s : Set α} {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {c : E}

def indicatorConstLp (p : ℝ≥0∞) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) : Lp E p μ :=
  MemLp.toLp (s.indicator fun _ => c) (memLp_indicator_const p hs c (Or.inr hμs))

theorem indicatorConstLp_add {c' : E} :
    indicatorConstLp p hs hμs c + indicatorConstLp p hs hμs c' =
    indicatorConstLp p hs hμs (c + c') := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_add, indicator_add]
  rfl

theorem indicatorConstLp_sub {c' : E} :
    indicatorConstLp p hs hμs c - indicatorConstLp p hs hμs c' =
    indicatorConstLp p hs hμs (c - c') := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_sub, indicator_sub]
  rfl

theorem indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c :=
  MemLp.coeFn_toLp (memLp_indicator_const p hs c (Or.inr hμs))

theorem indicatorConstLp_coeFn_mem : ∀ᵐ x : α ∂μ, x ∈ s → indicatorConstLp p hs hμs c x = c :=
  indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_mem hxs _)

theorem indicatorConstLp_coeFn_notMem : ∀ᵐ x : α ∂μ, x ∉ s → indicatorConstLp p hs hμs c x = 0 :=
  indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_notMem hxs _)

-- DISSOLVED: norm_indicatorConstLp

-- DISSOLVED: norm_indicatorConstLp_top

-- DISSOLVED: norm_indicatorConstLp'

theorem norm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ ≤ ‖c‖ * μ.real s ^ (1 / p.toReal) := by
  rw [indicatorConstLp, Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (eLpNorm_indicator_const_le _ _).trans_eq ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, measureReal_def,
    ENNReal.toReal_rpow, ENNReal.ofReal_toReal]
  finiteness

theorem nnnorm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖₊ ≤ ‖c‖₊ * (μ s).toNNReal ^ (1 / p.toReal) :=
  norm_indicatorConstLp_le

theorem enorm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ₑ ≤ ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  simpa [ENNReal.coe_rpow_of_nonneg, ENNReal.coe_toNNReal hμs, Lp.enorm_def, ← enorm_eq_nnnorm]
    using ENNReal.coe_le_coe.2 <| nnnorm_indicatorConstLp_le (c := c) (hμs := hμs)

set_option backward.proofsInPublic true in

theorem edist_indicatorConstLp_eq_enorm {t : Set α} {ht : MeasurableSet t} {hμt : μ t ≠ ∞} :
    edist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp p (hs.symmDiff ht) (by finiteness) c‖ₑ := by
  unfold indicatorConstLp
  rw [Lp.edist_toLp_toLp, eLpNorm_indicator_sub_indicator, Lp.enorm_toLp]

set_option backward.proofsInPublic true in

theorem dist_indicatorConstLp_eq_norm {t : Set α} {ht : MeasurableSet t} {hμt : μ t ≠ ∞} :
    dist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp p (hs.symmDiff ht) (by finiteness) c‖ := by
  -- Squeezed for performance reasons
  simp only [Lp.dist_edist, edist_indicatorConstLp_eq_enorm, enorm, ENNReal.coe_toReal,
    Lp.coe_nnnorm]

theorem tendsto_indicatorConstLp_set [hp₁ : Fact (1 ≤ p)] {β : Type*} {l : Filter β} {t : β → Set α}
    {ht : ∀ b, MeasurableSet (t b)} {hμt : ∀ b, μ (t b) ≠ ∞} (hp : p ≠ ∞)
    (h : Tendsto (fun b ↦ μ (t b ∆ s)) l (𝓝 0)) :
    Tendsto (fun b ↦ indicatorConstLp p (ht b) (hμt b) c) l (𝓝 (indicatorConstLp p hs hμs c)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hp₀ : p ≠ 0 := (one_pos.trans_le hp₁.out).ne'
  simp only [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp hp₀ hp]
  convert tendsto_const_nhds.mul
    (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).rpow_const _)
  · simp [ENNReal.toReal_eq_zero_iff, hp, hp₀]
  · simp

theorem continuous_indicatorConstLp_set [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X]
    {s : X → Set α} {hs : ∀ x, MeasurableSet (s x)} {hμs : ∀ x, μ (s x) ≠ ∞} (hp : p ≠ ∞)
    (h : ∀ x, Tendsto (fun y ↦ μ (s y ∆ s x)) (𝓝 x) (𝓝 0)) :
    Continuous fun x ↦ indicatorConstLp p (hs x) (hμs x) c :=
  continuous_iff_continuousAt.2 fun x ↦ tendsto_indicatorConstLp_set hp (h x)
