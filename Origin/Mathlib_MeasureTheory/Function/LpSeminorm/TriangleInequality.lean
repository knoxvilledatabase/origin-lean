/-
Extracted from MeasureTheory/Function/LpSeminorm/TriangleInequality.lean
Genuine: 18 of 19 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Triangle inequality for `Lp`-seminorm

In this file we prove several versions of the triangle inequality for the `Lp` seminorm,
as well as simple corollaries.
-/

open Filter

open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} {q : ℝ} {μ : Measure α} {f g : α → E}

theorem eLpNorm'_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hq1 : 1 ≤ q) : eLpNorm' (f + g) q μ ≤ eLpNorm' f q μ + eLpNorm' g q μ :=
  calc
    (∫⁻ a, (‖(f + g) a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) ≤
        (∫⁻ a, ((fun a => (‖f a‖₊ : ℝ≥0∞)) + fun a => (‖g a‖₊ : ℝ≥0∞)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, ← ENNReal.coe_add, ENNReal.coe_le_coe, nnnorm_add_le]
    _ ≤ eLpNorm' f q μ + eLpNorm' g q μ := ENNReal.lintegral_Lp_add_le hf.ennnorm hg.ennnorm hq1

alias snorm'_add_le := eLpNorm'_add_le

theorem eLpNorm'_add_le_of_le_one (hf : AEStronglyMeasurable f μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    eLpNorm' (f + g) q μ ≤ (2 : ℝ≥0∞) ^ (1 / q - 1) * (eLpNorm' f q μ + eLpNorm' g q μ) :=
  calc
    (∫⁻ a, (‖(f + g) a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) ≤
        (∫⁻ a, ((fun a => (‖f a‖₊ : ℝ≥0∞)) + fun a => (‖g a‖₊ : ℝ≥0∞)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, ← ENNReal.coe_add, ENNReal.coe_le_coe, nnnorm_add_le]
    _ ≤ (2 : ℝ≥0∞) ^ (1 / q - 1) * (eLpNorm' f q μ + eLpNorm' g q μ) :=
      ENNReal.lintegral_Lp_add_le_of_le_one hf.ennnorm hq0 hq1

alias snorm'_add_le_of_le_one := eLpNorm'_add_le_of_le_one

theorem eLpNormEssSup_add_le {f g : α → E} :
    eLpNormEssSup (f + g) μ ≤ eLpNormEssSup f μ + eLpNormEssSup g μ := by
  refine le_trans (essSup_mono_ae (Eventually.of_forall fun x => ?_)) (ENNReal.essSup_add_le _ _)
  simp_rw [Pi.add_apply, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  exact nnnorm_add_le _ _

alias snormEssSup_add_le := eLpNormEssSup_add_le

theorem eLpNorm_add_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp1 : 1 ≤ p) : eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_add_le]
  have hp1_real : 1 ≤ p.toReal := by
    rwa [← ENNReal.one_toReal, ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top]
  repeat rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_add_le hf hg hp1_real

alias snorm_add_le := eLpNorm_add_le

noncomputable def LpAddConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p ∈ Set.Ioo (0 : ℝ≥0∞) 1 then (2 : ℝ≥0∞) ^ (1 / p.toReal - 1) else 1

theorem LpAddConst_of_one_le {p : ℝ≥0∞} (hp : 1 ≤ p) : LpAddConst p = 1 := by
  rw [LpAddConst, if_neg]
  intro h
  exact lt_irrefl _ (h.2.trans_le hp)

theorem LpAddConst_zero : LpAddConst 0 = 1 := by
  rw [LpAddConst, if_neg]
  intro h
  exact lt_irrefl _ h.1

theorem LpAddConst_lt_top (p : ℝ≥0∞) : LpAddConst p < ∞ := by
  rw [LpAddConst]
  split_ifs with h
  · apply ENNReal.rpow_lt_top_of_nonneg _ ENNReal.two_ne_top
    rw [one_div, sub_nonneg, ← ENNReal.toReal_inv, ← ENNReal.one_toReal]
    exact ENNReal.toReal_mono (by simpa using h.1.ne') (ENNReal.one_le_inv.2 h.2.le)
  · exact ENNReal.one_lt_top

theorem eLpNorm_add_le' (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) : eLpNorm (f + g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp only [eLpNorm_exponent_zero, add_zero, mul_zero, le_zero_iff]
  rcases lt_or_le p 1 with (h'p | h'p)
  · simp only [eLpNorm_eq_eLpNorm' hp (h'p.trans ENNReal.one_lt_top).ne]
    convert eLpNorm'_add_le_of_le_one hf ENNReal.toReal_nonneg _
    · have : p ∈ Set.Ioo (0 : ℝ≥0∞) 1 := ⟨hp.bot_lt, h'p⟩
      simp only [LpAddConst, if_pos this]
    · simpa using ENNReal.toReal_mono ENNReal.one_ne_top h'p.le
  · simpa [LpAddConst_of_one_le h'p] using eLpNorm_add_le hf hg h'p

alias snorm_add_le' := eLpNorm_add_le'

variable (μ E)

-- DISSOLVED: exists_Lp_half

variable {μ E}

theorem eLpNorm_sub_le' (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) : eLpNorm (f - g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) := by
  simpa only [sub_eq_add_neg, eLpNorm_neg] using eLpNorm_add_le' hf hg.neg p

alias snorm_sub_le' := eLpNorm_sub_le'

theorem eLpNorm_sub_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp : 1 ≤ p) : eLpNorm (f - g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  simpa [LpAddConst_of_one_le hp] using eLpNorm_sub_le' hf hg p

alias snorm_sub_le := eLpNorm_sub_le

theorem eLpNorm_add_lt_top {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    eLpNorm (f + g) p μ < ∞ :=
  calc
    eLpNorm (f + g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf.aestronglyMeasurable hg.aestronglyMeasurable p
    _ < ∞ := by
      apply ENNReal.mul_lt_top (LpAddConst_lt_top p)
      exact ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩

alias snorm_add_lt_top := eLpNorm_add_lt_top

theorem eLpNorm'_sum_le {ι} {f : ι → α → E} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) (hq1 : 1 ≤ q) :
    eLpNorm' (∑ i ∈ s, f i) q μ ≤ ∑ i ∈ s, eLpNorm' (f i) q μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → E => eLpNorm' f q μ)
    (fun f => AEStronglyMeasurable f μ) (eLpNorm'_zero (zero_lt_one.trans_le hq1))
    (fun _f _g hf hg => eLpNorm'_add_le hf hg hq1) (fun _f _g hf hg => hf.add hg) _ hfs

alias snorm'_sum_le := eLpNorm'_sum_le

theorem eLpNorm_sum_le {ι} {f : ι → α → E} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) (hp1 : 1 ≤ p) :
    eLpNorm (∑ i ∈ s, f i) p μ ≤ ∑ i ∈ s, eLpNorm (f i) p μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → E => eLpNorm f p μ)
    (fun f => AEStronglyMeasurable f μ) eLpNorm_zero (fun _f _g hf hg => eLpNorm_add_le hf hg hp1)
    (fun _f _g hf hg => hf.add hg) _ hfs

alias snorm_sum_le := eLpNorm_sum_le

theorem Memℒp.add {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) : Memℒp (f + g) p μ :=
  ⟨AEStronglyMeasurable.add hf.1 hg.1, eLpNorm_add_lt_top hf hg⟩

theorem Memℒp.sub {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) : Memℒp (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem memℒp_finset_sum {ι} (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, Memℒp (f i) p μ) :
    Memℒp (fun a => ∑ i ∈ s, f i a) p μ := by
  haveI : DecidableEq ι := Classical.decEq _
  revert hf
  refine Finset.induction_on s ?_ ?_
  · simp only [zero_mem_ℒp', Finset.sum_empty, imp_true_iff]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem memℒp_finset_sum' {ι} (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, Memℒp (f i) p μ) :
    Memℒp (∑ i ∈ s, f i) p μ := by
  convert memℒp_finset_sum s hf using 1
  ext x
  simp

end MeasureTheory
