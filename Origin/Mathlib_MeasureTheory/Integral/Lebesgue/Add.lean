/-
Extracted from MeasureTheory/Integral/Lebesgue/Add.lean
Genuine: 14 of 15 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Monotone convergence theorem and addition of Lebesgue integrals

The monotone convergence theorem (aka Beppo Levi lemma) states that the Lebesgue integral and
supremum can be swapped for a pointwise monotone sequence of functions. This file first proves
several variants of this theorem, then uses it to show that the Lebesgue integral is additive
(assuming one of the functions is at least `AEMeasurable`) and respects multiplication by
a constant.
-/

namespace MeasureTheory

open Set Filter ENNReal Topology NNReal SimpleFunc

variable {α β : Type*} {m : MeasurableSpace α} {μ : Measure α}

local infixr:25 " →ₛ " => SimpleFunc

section MonotoneConvergence

theorem lintegral_iSup' {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) : ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  simp_rw [← iSup_apply]
  let p : α → (ℕ → ℝ≥0∞) → Prop := fun _ f' => Monotone f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := h_mono
  have h_ae_seq_mono : Monotone (aeSeq hf p) := by
    intro n m hnm x
    by_cases hx : x ∈ aeSeqSet hf p
    · exact aeSeq.prop_of_mem_aeSeqSet hf hx hnm
    · simp only [aeSeq, hx, if_false, le_rfl]
  rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  simp_rw [iSup_apply]
  rw [lintegral_iSup (aeSeq.measurable hf p) h_ae_seq_mono]
  congr with n
  exact lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae hf hp n)

theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 <| F x)) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 <| ∫⁻ x, F x ∂μ) := by
  have : Monotone fun n => ∫⁻ x, f n x ∂μ := fun i j hij =>
    lintegral_mono_ae (h_mono.mono fun x hx => hx hij)
  suffices key : ∫⁻ x, F x ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ by
    rw [key]
    exact tendsto_atTop_iSup this
  rw [← lintegral_iSup' hf h_mono]
  refine lintegral_congr_ae ?_
  filter_upwards [h_mono, h_tendsto] with _ hx_mono hx_tendsto using
    tendsto_nhds_unique hx_tendsto (tendsto_atTop_iSup hx_mono)

theorem lintegral_iSup_ae {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (h_mono : ∀ n, ∀ᵐ a ∂μ, f n a ≤ f n.succ a) : ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  classical
  let ⟨s, hs⟩ := exists_measurable_superset_of_null (ae_iff.1 (ae_all_iff.2 h_mono))
  let g n a := if a ∈ s then 0 else f n a
  have g_eq_f : ∀ᵐ a ∂μ, ∀ n, g n a = f n a :=
    (measure_eq_zero_iff_ae_notMem.1 hs.2.2).mono fun a ha n => if_neg ha
  calc
    ∫⁻ a, ⨆ n, f n a ∂μ = ∫⁻ a, ⨆ n, g n a ∂μ :=
      lintegral_congr_ae <| g_eq_f.mono fun a ha => by simp only [ha]
    _ = ⨆ n, ∫⁻ a, g n a ∂μ :=
      (lintegral_iSup (fun n => measurable_const.piecewise hs.2.1 (hf n))
        (monotone_nat_of_le_succ fun n a => ?_))
    _ = ⨆ n, ∫⁻ a, f n a ∂μ := by simp only [lintegral_congr_ae (g_eq_f.mono fun _a ha => ha _)]
  simp only [g]
  split_ifs with h
  · rfl
  · have := Set.notMem_subset hs.1 h
    simp only [not_forall, not_le, mem_setOf_eq, not_exists, not_lt] at this
    exact this n

open Encodable in

theorem lintegral_iSup_directed_of_measurable [Countable β] {f : β → α → ℝ≥0∞}
    (hf : ∀ b, Measurable (f b)) (h_directed : Directed (· ≤ ·) f) :
    ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ := by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · simp
  inhabit β
  have : ∀ a, ⨆ b, f b a = ⨆ n, f (h_directed.sequence f n) a := by
    intro a
    refine le_antisymm (iSup_le fun b => ?_) (iSup_le fun n => le_iSup (fun n => f n a) _)
    exact le_iSup_of_le (encode b + 1) (h_directed.le_sequence b a)
  calc
    ∫⁻ a, ⨆ b, f b a ∂μ = ∫⁻ a, ⨆ n, f (h_directed.sequence f n) a ∂μ := by simp only [this]
    _ = ⨆ n, ∫⁻ a, f (h_directed.sequence f n) a ∂μ :=
      (lintegral_iSup (fun n => hf _) h_directed.sequence_mono)
    _ = ⨆ b, ∫⁻ a, f b a ∂μ := by
      refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun b => ?_)
      · exact le_iSup (fun b => ∫⁻ a, f b a ∂μ) _
      · exact le_iSup_of_le (encode b + 1) (lintegral_mono <| h_directed.le_sequence b)

theorem lintegral_iSup_directed [Countable β] {f : β → α → ℝ≥0∞} (hf : ∀ b, AEMeasurable (f b) μ)
    (h_directed : Directed (· ≤ ·) f) : ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ := by
  simp_rw [← iSup_apply]
  let p : α → (β → ENNReal) → Prop := fun x f' => Directed LE.le f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := by
    filter_upwards [] with x i j
    obtain ⟨z, hz₁, hz₂⟩ := h_directed i j
    exact ⟨z, hz₁ x, hz₂ x⟩
  have h_ae_seq_directed : Directed LE.le (aeSeq hf p) := by
    intro b₁ b₂
    obtain ⟨z, hz₁, hz₂⟩ := h_directed b₁ b₂
    refine ⟨z, ?_, ?_⟩ <;>
      · intro x
        by_cases hx : x ∈ aeSeqSet hf p
        · repeat rw [aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet hf hx]
          apply_rules [hz₁, hz₂]
        · simp only [aeSeq, hx, if_false]
          exact le_rfl
  convert lintegral_iSup_directed_of_measurable (aeSeq.measurable hf p) h_ae_seq_directed using 1
  · simp_rw [← iSup_apply]
    rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  · congr 1
    ext1 b
    rw [lintegral_congr_ae]
    apply EventuallyEq.symm
    exact aeSeq.aeSeq_n_eq_fun_n_ae hf hp _

private theorem lintegral_liminf_nat_le' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, AEMeasurable (f n) μ) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  calc
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ = ∫⁻ a, ⨆ n : ℕ, ⨅ i ≥ n, f i a ∂μ := by
      simp only [liminf_eq_iSup_iInf_of_nat]
    _ = ⨆ n : ℕ, ∫⁻ a, ⨅ i ≥ n, f i a ∂μ :=
      (lintegral_iSup' (fun _ => .biInf _ (to_countable _) (fun i _ ↦ h_meas i))
        (ae_of_all μ fun _ _ _ hnm => iInf_le_iInf_of_subset fun _ hi => le_trans hnm hi))
    _ ≤ ⨆ n : ℕ, ⨅ i ≥ n, ∫⁻ a, f i a ∂μ := iSup_mono fun _ => le_iInf₂_lintegral _
    _ = atTop.liminf fun n => ∫⁻ a, f n a ∂μ := Filter.liminf_eq_iSup_iInf_of_nat.symm

theorem lintegral_liminf_le' {ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι}
    [IsCountablyGenerated u] (h_meas : ∀ i, AEMeasurable (f i) μ) :
    ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u := by
  by_cases! hu : ¬ u.NeBot
  · simp_all
  · obtain ⟨g, hg⟩ : ∃ g : ℕ → ι,
        Tendsto (fun n => ∫⁻ a, f (g n) a ∂μ) atTop (𝓝 (liminf (fun i => ∫⁻ a, f i a ∂μ) u)) ∧
        Tendsto g atTop u :=
      exists_seq_tendsto_liminf
    calc
    _ ≤ ∫⁻ a, liminf (fun n => f (g n) a) atTop ∂μ :=
      lintegral_mono fun a => hg.2.liminf_le_liminf_comp
    _ ≤ liminf (fun n => ∫⁻ a, f (g n) a ∂μ) atTop :=
      lintegral_liminf_nat_le' (fun n => h_meas (g n))
    _ = _ := hg.1.liminf_eq

theorem lintegral_liminf_le {ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι}
    [IsCountablyGenerated u] (h_meas : ∀ i, Measurable (f i)) :
    ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u :=
  lintegral_liminf_le' fun n => (h_meas n).aemeasurable

end MonotoneConvergence

section Add

theorem lintegral_eq_iSup_eapprox_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ⨆ n, (eapprox f n).lintegral μ :=
  calc
    ∫⁻ a, f a ∂μ = ∫⁻ a, ⨆ n, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      congr; ext a; rw [iSup_eapprox_apply hf]
    _ = ⨆ n, ∫⁻ a, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      apply lintegral_iSup
      · fun_prop
      · intro i j h
        exact monotone_eapprox f h
    _ = ⨆ n, (eapprox f n).lintegral μ := by
      congr; ext n; rw [(eapprox f n).lintegral_eq_lintegral]

theorem lintegral_eq_iSup_eapprox_lintegral' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a ∂μ = ⨆ n, (eapprox (hf.mk f) n).lintegral μ := by
  rw [lintegral_congr_ae hf.ae_eq_mk, lintegral_eq_iSup_eapprox_lintegral hf.measurable_mk]

lemma lintegral_eapprox_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    (eapprox f n).lintegral μ ≤ ∫⁻ x, f x ∂μ := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  exact le_iSup (fun n ↦ (eapprox f n).lintegral μ) n

lemma measure_support_eapprox_lt_top {f : α → ℝ≥0∞} (hf_meas : Measurable f)
    (hf : ∫⁻ x, f x ∂μ ≠ ∞) (n : ℕ) :
    μ (Function.support (eapprox f n)) < ∞ :=
  measure_support_lt_top_of_lintegral_ne_top <|
    ((lintegral_eapprox_le_lintegral hf_meas n).trans_lt hf.lt_top).ne

theorem le_lintegral_add (f g : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ ≤ ∫⁻ a, f a + g a ∂μ := by
  simp only [lintegral]
  refine ENNReal.biSup_add_biSup_le' (p := fun h : α →ₛ ℝ≥0∞ => h ≤ f)
    (q := fun h : α →ₛ ℝ≥0∞ => h ≤ g) ⟨0, zero_le f⟩ ⟨0, zero_le g⟩ fun f' hf' g' hg' => ?_
  exact le_iSup₂_of_le (f' + g') (add_le_add hf' hg') (add_lintegral _ _).ge

theorem lintegral_add_aux {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  calc
    ∫⁻ a, f a + g a ∂μ =
        ∫⁻ a, (⨆ n, (eapprox f n : α → ℝ≥0∞) a) + ⨆ n, (eapprox g n : α → ℝ≥0∞) a ∂μ := by
      simp only [iSup_eapprox_apply, hf, hg]
    _ = ∫⁻ a, ⨆ n, (eapprox f n + eapprox g n : α → ℝ≥0∞) a ∂μ := by
      congr; funext a
      rw [ENNReal.iSup_add_iSup_of_monotone]
      · simp only [Pi.add_apply]
      · intro i j h
        exact monotone_eapprox _ h a
      · intro i j h
        exact monotone_eapprox _ h a
    _ = ⨆ n, (eapprox f n).lintegral μ + (eapprox g n).lintegral μ := by
      rw [lintegral_iSup]
      · congr
        funext n
        rw [← SimpleFunc.add_lintegral, ← SimpleFunc.lintegral_eq_lintegral]
        simp only [Pi.add_apply, SimpleFunc.coe_add]
      · fun_prop
      · intro i j h a
        dsimp
        gcongr <;> exact monotone_eapprox _ h _
    _ = (⨆ n, (eapprox f n).lintegral μ) + ⨆ n, (eapprox g n).lintegral μ := by
      refine (ENNReal.iSup_add_iSup_of_monotone ?_ ?_).symm <;>
        · intro i j h
          exact SimpleFunc.lintegral_mono (monotone_eapprox _ h) le_rfl
    _ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
      rw [lintegral_eq_iSup_eapprox_lintegral hf, lintegral_eq_iSup_eapprox_lintegral hg]
