/-
Extracted from MeasureTheory/Measure/Lebesgue/Basic.lean
Genuine: 47 of 62 | Dissolved: 9 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Lebesgue measure on the real line and on `ℝⁿ`

We show that the Lebesgue measure on the real line (constructed as a particular case of additive
Haar measure on inner product spaces) coincides with the Stieltjes measure associated
to the function `x ↦ x`. We deduce properties of this measure on `ℝ`, and then of the product
Lebesgue measure on `ℝⁿ`. In particular, we prove that they are translation invariant.

We show that, on `ℝⁿ`, a linear map acts on Lebesgue measure by rescaling it through the absolute
value of its determinant, in `Real.map_linearMap_volume_pi_eq_smul_volume_pi`.

More properties of the Lebesgue measure are deduced from this in
`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`, where they are proved more generally for any
additive Haar measure on a finite-dimensional real vector space.
-/

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

open ENNReal (ofReal)

open scoped ENNReal NNReal Topology

/-!
### Definition of the Lebesgue measure and lengths of intervals
-/

namespace Real

variable {ι : Type*} [Fintype ι]

theorem volume_eq_stieltjes_id : (volume : Measure ℝ) = StieltjesFunction.id.measure := by
  haveI : IsAddLeftInvariant StieltjesFunction.id.measure :=
    ⟨fun a =>
      Eq.symm <|
        Real.measure_ext_Ioo_rat fun p q => by
          simp only [Measure.map_apply (measurable_const_add a) measurableSet_Ioo,
            sub_sub_sub_cancel_right, StieltjesFunction.measure_Ioo, StieltjesFunction.id_leftLim,
            StieltjesFunction.id_apply, id, preimage_const_add_Ioo]⟩
  have A : StieltjesFunction.id.measure (stdOrthonormalBasis ℝ ℝ).toBasis.parallelepiped = 1 := by
    change StieltjesFunction.id.measure (parallelepiped (stdOrthonormalBasis ℝ ℝ)) = 1
    rcases parallelepiped_orthonormalBasis_one_dim (stdOrthonormalBasis ℝ ℝ) with (H | H) <;>
      simp only [H, StieltjesFunction.measure_Icc, StieltjesFunction.id_apply, id, tsub_zero,
        StieltjesFunction.id_leftLim, sub_neg_eq_add, zero_add, ENNReal.ofReal_one]
  conv_rhs =>
    rw [addHaarMeasure_unique StieltjesFunction.id.measure
        (stdOrthonormalBasis ℝ ℝ).toBasis.parallelepiped, A]
  simp only [volume, Basis.addHaar, one_smul]

theorem volume_val (s) : volume s = StieltjesFunction.id.measure s := by
  simp [volume_eq_stieltjes_id]

@[simp]
theorem volume_Ico {a b : ℝ} : volume (Ico a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
theorem volume_Icc {a b : ℝ} : volume (Icc a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
theorem volume_Ioo {a b : ℝ} : volume (Ioo a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
theorem volume_Ioc {a b : ℝ} : volume (Ioc a b) = ofReal (b - a) := by simp [volume_val]

theorem volume_singleton {a : ℝ} : volume ({a} : Set ℝ) = 0 := by simp [volume_val]

theorem volume_univ : volume (univ : Set ℝ) = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r =>
    calc
      (r : ℝ≥0∞) = volume (Icc (0 : ℝ) r) := by simp
      _ ≤ volume univ := measure_mono (subset_univ _)

@[simp]
theorem volume_ball (a r : ℝ) : volume (Metric.ball a r) = ofReal (2 * r) := by
  rw [ball_eq_Ioo, volume_Ioo, ← sub_add, add_sub_cancel_left, two_mul]

@[simp]
theorem volume_closedBall (a r : ℝ) : volume (Metric.closedBall a r) = ofReal (2 * r) := by
  rw [closedBall_eq_Icc, volume_Icc, ← sub_add, add_sub_cancel_left, two_mul]

@[simp]
theorem volume_emetric_ball (a : ℝ) (r : ℝ≥0∞) : volume (EMetric.ball a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.emetric_ball_top, volume_univ, two_mul, _root_.top_add]
  · lift r to ℝ≥0 using hr
    rw [Metric.emetric_ball_nnreal, volume_ball, two_mul, ← NNReal.coe_add,
      ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, two_mul]

@[simp]
theorem volume_emetric_closedBall (a : ℝ) (r : ℝ≥0∞) : volume (EMetric.closedBall a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [EMetric.closedBall_top, volume_univ, two_mul, _root_.top_add]
  · lift r to ℝ≥0 using hr
    rw [Metric.emetric_closedBall_nnreal, volume_closedBall, two_mul, ← NNReal.coe_add,
      ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, two_mul]

instance noAtoms_volume : NoAtoms (volume : Measure ℝ) :=
  ⟨fun _ => volume_singleton⟩

@[simp]
theorem volume_interval {a b : ℝ} : volume (uIcc a b) = ofReal |b - a| := by
  rw [← Icc_min_max, volume_Icc, max_sub_min_eq_abs]

@[simp]
theorem volume_Ioi {a : ℝ} : volume (Ioi a) = ∞ :=
  top_unique <|
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : ℝ≥0∞) = volume (Ioo a (a + n)) := by simp
        _ ≤ volume (Ioi a) := measure_mono Ioo_subset_Ioi_self

@[simp]
theorem volume_Ici {a : ℝ} : volume (Ici a) = ∞ := by rw [← measure_congr Ioi_ae_eq_Ici]; simp

@[simp]
theorem volume_Iio {a : ℝ} : volume (Iio a) = ∞ :=
  top_unique <|
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : ℝ≥0∞) = volume (Ioo (a - n) a) := by simp
        _ ≤ volume (Iio a) := measure_mono Ioo_subset_Iio_self

@[simp]
theorem volume_Iic {a : ℝ} : volume (Iic a) = ∞ := by rw [← measure_congr Iio_ae_eq_Iic]; simp

instance locallyFinite_volume : IsLocallyFiniteMeasure (volume : Measure ℝ) :=
  ⟨fun x =>
    ⟨Ioo (x - 1) (x + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩, by
      simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top]⟩⟩

instance isFiniteMeasure_restrict_Icc (x y : ℝ) : IsFiniteMeasure (volume.restrict (Icc x y)) :=
  ⟨by simp⟩

instance isFiniteMeasure_restrict_Ico (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ico x y)) :=
  ⟨by simp⟩

instance isFiniteMeasure_restrict_Ioc (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ioc x y)) :=
  ⟨by simp⟩

instance isFiniteMeasure_restrict_Ioo (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ioo x y)) :=
  ⟨by simp⟩

theorem volume_le_diam (s : Set ℝ) : volume s ≤ EMetric.diam s := by
  by_cases hs : Bornology.IsBounded s
  · rw [Real.ediam_eq hs, ← volume_Icc]
    exact volume.mono hs.subset_Icc_sInf_sSup
  · rw [Metric.ediam_of_unbounded hs]; exact le_top

theorem _root_.Filter.Eventually.volume_pos_of_nhds_real {p : ℝ → Prop} {a : ℝ}
    (h : ∀ᶠ x in 𝓝 a, p x) : (0 : ℝ≥0∞) < volume { x | p x } := by
  rcases h.exists_Ioo_subset with ⟨l, u, hx, hs⟩
  refine lt_of_lt_of_le ?_ (measure_mono hs)
  simpa [-mem_Ioo] using hx.1.trans hx.2

/-!
### Volume of a box in `ℝⁿ`
-/

theorem volume_Icc_pi {a b : ι → ℝ} : volume (Icc a b) = ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [← pi_univ_Icc, volume_pi_pi]
  simp only [Real.volume_Icc]

@[simp]
theorem volume_Icc_pi_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (Icc a b)).toReal = ∏ i, (b i - a i) := by
  simp only [volume_Icc_pi, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

theorem volume_pi_Ioo {a b : ι → ℝ} :
    volume (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ioo_ae_eq_Icc).trans volume_Icc_pi

@[simp]
theorem volume_pi_Ioo_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi univ fun i => Ioo (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ioo, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

theorem volume_pi_Ioc {a b : ι → ℝ} :
    volume (pi univ fun i => Ioc (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ioc_ae_eq_Icc).trans volume_Icc_pi

@[simp]
theorem volume_pi_Ioc_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi univ fun i => Ioc (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ioc, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

theorem volume_pi_Ico {a b : ι → ℝ} :
    volume (pi univ fun i => Ico (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ico_ae_eq_Icc).trans volume_Icc_pi

@[simp]
theorem volume_pi_Ico_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi univ fun i => Ico (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ico, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

@[simp]
nonrec theorem volume_pi_ball (a : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_ball a hr, volume_ball, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr.le) _).symm

@[simp]
nonrec theorem volume_pi_closedBall (a : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_closedBall a hr, volume_closedBall, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr) _).symm

theorem volume_pi_le_prod_diam (s : Set (ι → ℝ)) :
    volume s ≤ ∏ i : ι, EMetric.diam (Function.eval i '' s) :=
  calc
    volume s ≤ volume (pi univ fun i => closure (Function.eval i '' s)) :=
      volume.mono <|
        Subset.trans (subset_pi_eval_image univ s) <| pi_mono fun _ _ => subset_closure
    _ = ∏ i, volume (closure <| Function.eval i '' s) := volume_pi_pi _
    _ ≤ ∏ i : ι, EMetric.diam (Function.eval i '' s) :=
      Finset.prod_le_prod' fun _ _ => (volume_le_diam _).trans_eq (EMetric.diam_closure _)

theorem volume_pi_le_diam_pow (s : Set (ι → ℝ)) : volume s ≤ EMetric.diam s ^ Fintype.card ι :=
  calc
    volume s ≤ ∏ i : ι, EMetric.diam (Function.eval i '' s) := volume_pi_le_prod_diam s
    _ ≤ ∏ _i : ι, (1 : ℝ≥0) * EMetric.diam s :=
      (Finset.prod_le_prod' fun i _ => (LipschitzWith.eval i).ediam_image_le s)
    _ = EMetric.diam s ^ Fintype.card ι := by
      simp only [ENNReal.coe_one, one_mul, Finset.prod_const, Fintype.card]

/-!
### Images of the Lebesgue measure under multiplication in ℝ
-/

-- DISSOLVED: smul_map_volume_mul_left

-- DISSOLVED: map_volume_mul_left

-- DISSOLVED: volume_preimage_mul_left

-- DISSOLVED: smul_map_volume_mul_right

-- DISSOLVED: map_volume_mul_right

-- DISSOLVED: volume_preimage_mul_right

/-!
### Images of the Lebesgue measure under translation/linear maps in ℝⁿ
-/

open Matrix

-- DISSOLVED: smul_map_diagonal_volume_pi

theorem volume_preserving_transvectionStruct [DecidableEq ι] (t : TransvectionStruct ι ℝ) :
    MeasurePreserving (toLin' t.toMatrix) := by
  /- We use `lmarginal` to conveniently use Fubini's theorem.
    Along the coordinate where there is a shearing, it acts like a
    translation, and therefore preserves Lebesgue. -/
  have ht : Measurable (toLin' t.toMatrix) :=
    (toLin' t.toMatrix).continuous_of_finiteDimensional.measurable
  refine ⟨ht, ?_⟩
  refine (pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ ↦ hs i
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht, volume_pi]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, mulVec_stdBasisMatrix, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ ↦ indicator (univ.pi s) 1 (Function.update x t_i xᵢ)]

-- DISSOLVED: map_matrix_volume_pi_eq_smul_volume_pi

-- DISSOLVED: map_linearMap_volume_pi_eq_smul_volume_pi

end Real

section regionBetween

variable {α : Type*}

def regionBetween (f g : α → ℝ) (s : Set α) : Set (α × ℝ) :=
  { p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioo (f p.1) (g p.1) }

theorem regionBetween_subset (f g : α → ℝ) (s : Set α) : regionBetween f g s ⊆ s ×ˢ univ := by
  simpa only [prod_univ, regionBetween, Set.preimage, setOf_subset_setOf] using fun a => And.left

variable [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {s : Set α}

theorem measurableSet_regionBetween (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    MeasurableSet (regionBetween f g s) := by
  dsimp only [regionBetween, Ioo, mem_setOf_eq, setOf_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

theorem measurableSet_region_between_oc (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Ioc (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Ioc, mem_setOf_eq, setOf_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

theorem measurableSet_region_between_co (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Ico (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Ico, mem_setOf_eq, setOf_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

theorem measurableSet_region_between_cc (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Icc (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Icc, mem_setOf_eq, setOf_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

theorem measurableSet_graph (hf : Measurable f) :
    MeasurableSet { p : α × ℝ | p.snd = f p.fst } := by
  simpa using measurableSet_region_between_cc hf hf MeasurableSet.univ

theorem volume_regionBetween_eq_lintegral' (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    μ.prod volume (regionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ := by
  classical
    rw [Measure.prod_apply]
    · have h :
        (fun x => volume { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) }) =
          s.indicator fun x => ENNReal.ofReal (g x - f x) := by
        funext x
        rw [indicator_apply]
        split_ifs with h
        · have hx : { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) } = Ioo (f x) (g x) := by simp [h, Ioo]
          simp only [hx, Real.volume_Ioo, sub_zero]
        · have hx : { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) } = ∅ := by simp [h]
          simp only [hx, measure_empty]
      dsimp only [regionBetween, preimage_setOf_eq]
      rw [h, lintegral_indicator] <;> simp only [hs, Pi.sub_apply]
    · exact measurableSet_regionBetween hf hg hs

theorem volume_regionBetween_eq_lintegral [SFinite μ] (hf : AEMeasurable f (μ.restrict s))
    (hg : AEMeasurable g (μ.restrict s)) (hs : MeasurableSet s) :
    μ.prod volume (regionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ := by
  have h₁ :
    (fun y => ENNReal.ofReal ((g - f) y)) =ᵐ[μ.restrict s] fun y =>
      ENNReal.ofReal ((AEMeasurable.mk g hg - AEMeasurable.mk f hf) y) :=
    (hg.ae_eq_mk.sub hf.ae_eq_mk).fun_comp ENNReal.ofReal
  have h₂ :
    (μ.restrict s).prod volume (regionBetween f g s) =
      (μ.restrict s).prod volume
        (regionBetween (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s) := by
    apply measure_congr
    apply EventuallyEq.rfl.inter
    exact
      ((quasiMeasurePreserving_fst.ae_eq_comp hf.ae_eq_mk).comp₂ _ EventuallyEq.rfl).inter
        (EventuallyEq.rfl.comp₂ _ <| quasiMeasurePreserving_fst.ae_eq_comp hg.ae_eq_mk)
  rw [lintegral_congr_ae h₁, ←
    volume_regionBetween_eq_lintegral' hf.measurable_mk hg.measurable_mk hs]
  convert h₂ using 1
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact (Measure.restrict_eq_self _ (regionBetween_subset f g s)).symm
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact
      (Measure.restrict_eq_self _
          (regionBetween_subset (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s)).symm

lemma nullMeasurableSet_regionBetween (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Ioo (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (AEMeasurable.fst f_mble) measurable_snd.aemeasurable
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (AEMeasurable.fst g_mble)

lemma nullMeasurableSet_region_between_oc (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Ioc (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (AEMeasurable.fst f_mble) measurable_snd.aemeasurable
  · change NullMeasurableSet {p : α × ℝ | p.snd ≤ g p.fst} (μ.prod volume)
    rw [show {p : α × ℝ | p.snd ≤ g p.fst} = {p : α × ℝ | g p.fst < p.snd}ᶜ by
          ext p
          simp only [mem_setOf_eq, mem_compl_iff, not_lt]]
    exact (nullMeasurableSet_lt (AEMeasurable.fst g_mble) measurable_snd.aemeasurable).compl

lemma nullMeasurableSet_region_between_co (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Ico (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × ℝ | f p.fst ≤ p.snd} (μ.prod volume)
    rw [show {p : α × ℝ | f p.fst ≤ p.snd} = {p : α × ℝ | p.snd < f p.fst}ᶜ by
          ext p
          simp only [mem_setOf_eq, mem_compl_iff, not_lt]]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (AEMeasurable.fst f_mble)).compl
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (AEMeasurable.fst g_mble)

lemma nullMeasurableSet_region_between_cc (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Icc (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × ℝ | f p.fst ≤ p.snd} (μ.prod volume)
    rw [show {p : α × ℝ | f p.fst ≤ p.snd} = {p : α × ℝ | p.snd < f p.fst}ᶜ by
          ext p
          simp only [mem_setOf_eq, mem_compl_iff, not_lt]]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (AEMeasurable.fst f_mble)).compl
  · change NullMeasurableSet {p : α × ℝ | p.snd ≤ g p.fst} (μ.prod volume)
    rw [show {p : α × ℝ | p.snd ≤ g p.fst} = {p : α × ℝ | g p.fst < p.snd}ᶜ by
          ext p
          simp only [mem_setOf_eq, mem_compl_iff, not_lt]]
    exact (nullMeasurableSet_lt (AEMeasurable.fst g_mble) measurable_snd.aemeasurable).compl

end regionBetween

theorem ae_restrict_of_ae_restrict_inter_Ioo {μ : Measure ℝ} [NoAtoms μ] {s : Set ℝ} {p : ℝ → Prop}
    (h : ∀ a b, a ∈ s → b ∈ s → a < b → ∀ᵐ x ∂μ.restrict (s ∩ Ioo a b), p x) :
    ∀ᵐ x ∂μ.restrict s, p x := by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s → Set ℝ := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_diff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    ∃ A : Set (↥s × ↥s), A.Countable ∧ ⋃ i ∈ A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have : s ⊆ s \ u ∪ ⋃ p ∈ A, s ∩ T p := by
    intro x hx
    by_cases h'x : x ∈ ⋃ i : ↥s × ↥s, T i
    · rw [← hA] at h'x
      obtain ⟨p, pA, xp⟩ : ∃ p : ↥s × ↥s, p ∈ A ∧ x ∈ T p := by
        simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using h'x
      right
      exact mem_biUnion pA ⟨hx, xp⟩
    · exact Or.inl ⟨hx, h'x⟩
  apply ae_restrict_of_ae_restrict_of_subset this
  rw [ae_restrict_union_iff, ae_restrict_biUnion_iff _ A_count]
  constructor
  · have : μ.restrict (s \ u) = 0 := by simp only [restrict_eq_zero, hfinite.measure_zero]
    simp only [this, ae_zero, eventually_bot]
  · rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    dsimp [T]
    rcases le_or_lt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, restrict_empty, ae_zero, eventually_bot]
    · exact h a b as bs hab

theorem ae_of_mem_of_ae_of_mem_inter_Ioo {μ : Measure ℝ} [NoAtoms μ] {s : Set ℝ} {p : ℝ → Prop}
    (h : ∀ a b, a ∈ s → b ∈ s → a < b → ∀ᵐ x ∂μ, x ∈ s ∩ Ioo a b → p x) :
    ∀ᵐ x ∂μ, x ∈ s → p x := by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s → Set ℝ := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_diff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    ∃ A : Set (↥s × ↥s), A.Countable ∧ ⋃ i ∈ A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have M : ∀ᵐ x ∂μ, x ∉ s \ u := hfinite.countable.ae_not_mem _
  have M' : ∀ᵐ x ∂μ, ∀ (i : ↥s × ↥s), i ∈ A → x ∈ s ∩ T i → p x := by
    rw [ae_ball_iff A_count]
    rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    change ∀ᵐ x : ℝ ∂μ, x ∈ s ∩ Ioo a b → p x
    rcases le_or_lt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, IsEmpty.forall_iff, eventually_true,
        mem_empty_iff_false]
    · exact h a b as bs hab
  filter_upwards [M, M'] with x hx h'x
  intro xs
  by_cases Hx : x ∈ ⋃ i : ↥s × ↥s, T i
  · rw [← hA] at Hx
    obtain ⟨p, pA, xp⟩ : ∃ p : ↥s × ↥s, p ∈ A ∧ x ∈ T p := by
      simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using Hx
    apply h'x p pA ⟨xs, xp⟩
  · exact False.elim (hx ⟨xs, Hx⟩)
