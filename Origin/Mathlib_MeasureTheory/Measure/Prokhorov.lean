/-
Extracted from MeasureTheory/Measure/Prokhorov.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Prokhorov theorem

We prove statements about the compactness of sets of finite measures or probability measures,
notably several versions of Prokhorov theorem on tight sets of probability measures.

## Main statements

* `instCompactSpaceProbabilityMeasure` proves that the space of probability measures on a compact
  space is itself compact
* `isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le`: Given a sequence of compact
  sets `Kₙ` and a sequence `uₙ` tending to zero, the probability measures giving mass at most `uₙ`
  to the complement of `Kₙ` form a compact set.
* `isCompact_closure_of_isTightMeasureSet`: Given a tight set of probability measures, its closure
  is compact.

Versions are also given for finite measures.

## Implementation

We do not assume second-countability or metrizability.

For the compactness of the space of probability measures in a compact space, we argue that every
ultrafilter converges, using the Riesz-Markov-Kakutani theorem to construct the limiting measure
in terms of its integrals against continuous functions.

For Prokhorov theorem `isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le`,
we rely on the compactness of the space of measures inside each compact set to get convergence
of the restriction there, and argue that the full measure converges to the sum of the individual
limits of the disjointed components. There is a subtlety that the space of finite measures
giving mass `uₙ` to `Kₙᶜ` doesn't have to be closed in our general setting, but we only need to
find *a* limit satisfying this condition. To ensure this, we need a technical condition
(monotonicity of `K` or normality of the space). In the first case, the bound follows readily
from the construction. In the second case, we modify the individual limits
(again using Riesz-Markov-Kakutani) to make sure that they are inner-regular, and then one can
check the condition.
-/

open scoped ENNReal NNReal CompactlySupported

open Filter Function Set Topology TopologicalSpace MeasureTheory BoundedContinuousFunction

  MeasureTheory.FiniteMeasure

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]

variable (E) in

theorem isCompact_setOf_finiteMeasure_le_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C} := by
  /- To prove the compactness, we will show that any sequence has a converging subsequence, in
  ultrafilters terms as things are not second countable. The integral against any bounded continuous
  function has a limit along the ultrafilter, by compactness of real intervals and the mass control.
  The limit is a monotone linear form. By the Riesz-Markov-Kakutani theorem, it comes from a
  measure. This measure is finite, of mass at most `C`. It provides the desired limit
  for the ultrafilter. -/
  apply isCompact_iff_ultrafilter_le_nhds'.2 (fun f hf ↦ ?_)
  have L (g : C_c(E, ℝ)) :
      ∃ x ∈ Icc (-C * ‖g.toBoundedContinuousFunction‖) (C * ‖g.toBoundedContinuousFunction‖),
      Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, g x ∂μ) f (𝓝 x) := by
    simp only [Tendsto, ← Ultrafilter.coe_map]
    apply IsCompact.ultrafilter_le_nhds' isCompact_Icc
    simp only [neg_mul, Ultrafilter.mem_map]
    filter_upwards [hf] with μ hμ
    simp only [mem_preimage, mem_Icc]
    refine ⟨?_, ?_⟩
    · calc - (C * ‖g.toBoundedContinuousFunction‖)
      _ ≤ ∫ (x : E), - ‖g.toBoundedContinuousFunction‖ ∂μ := by
        simp only [integral_const, smul_eq_mul, mul_neg, neg_le_neg_iff]
        gcongr
        exact hμ
      _ ≤ ∫ x, g x ∂μ := by
        gcongr
        · simp
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · intro x
          apply neg_le_of_abs_le
          exact g.toBoundedContinuousFunction.norm_coe_le_norm x
    · calc ∫ x, g x ∂μ
      _ ≤ ∫ (x : E), ‖g.toBoundedContinuousFunction‖ ∂μ := by
        gcongr
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · simp
        · intro x
          apply le_of_abs_le
          exact g.toBoundedContinuousFunction.norm_coe_le_norm x
      _ ≤ C * ‖g.toBoundedContinuousFunction‖ := by
        simp only [integral_const, smul_eq_mul]
        gcongr
        exact hμ
  choose Λ h₀Λ hΛ using L
  let Λ' : C_c(E, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := Λ
    map_add' g g' := by
      have : Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, g x + g' x ∂μ) f (𝓝 (Λ g + Λ g')) := by
        convert (hΛ g).add (hΛ g')
        rw [integral_add]
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · exact g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport
      exact tendsto_nhds_unique (hΛ (g + g')) this
    map_smul' c g := by
      have : Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, c • g x ∂μ) f (𝓝 (c • Λ g)) := by
        convert (hΛ g).const_smul c
        rw [integral_smul]
      exact tendsto_nhds_unique (hΛ (c • g)) this
    monotone' g g' hgg' := by
      apply le_of_tendsto_of_tendsto' (hΛ g) (hΛ g') (fun μ ↦ ?_)
      apply integral_mono _ _ hgg'
      · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
      · exact g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport }
  let μlim := RealRMK.rieszMeasure Λ'
  have μlim_le : μlim univ ≤ ENNReal.ofReal C := by
    let o : C_c(E, ℝ) :=
    { toFun := 1
      hasCompactSupport' := HasCompactSupport.of_compactSpace 1 }
    have : μlim univ ≤ ENNReal.ofReal (Λ' o) := RealRMK.rieszMeasure_le_of_eq_one Λ'
      (fun x ↦ by simp [o]) isCompact_univ (fun x ↦ by simp [o])
    apply this.trans
    gcongr
    apply le_of_tendsto (hΛ o)
    filter_upwards [hf] with μ hμ using by simpa [o] using hμ
  let μlim' : FiniteMeasure E := ⟨μlim, ⟨μlim_le.trans_lt (by simp)⟩⟩
  refine ⟨μlim', ?_, ?_⟩
  · simp only [mem_setOf_eq, FiniteMeasure.mk_apply, μlim', FiniteMeasure.mass]
    rw [show C = (ENNReal.ofReal ↑C).toNNReal by simp]
    exact ENNReal.toNNReal_mono (by simp) μlim_le
  change Tendsto id f (𝓝 μlim')
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
  let g' : C_c(E, ℝ) :=
  { toFun := g
    hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  convert hΛ g'
  change ∫ (x : E), g' x ∂μlim' = Λ g'
  simp only [FiniteMeasure.toMeasure_mk, RealRMK.integral_rieszMeasure, μlim', μlim]
  rfl

variable (E) in

lemma isCompact_setOf_finiteMeasure_eq_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass = C} := by
  have : {μ : FiniteMeasure E | μ.mass = C} = {μ | μ.mass ≤ C} ∩ {μ | μ.mass = C} := by grind
  rw [this]
  apply IsCompact.inter_right (isCompact_setOf_finiteMeasure_le_of_compactSpace E C)
  exact isClosed_eq (by fun_prop) (by fun_prop)

-- INSTANCE (free from Core): [CompactSpace

lemma isCompact_setOf_finiteMeasure_le_of_isCompact
    (C : ℝ≥0) {K : Set E} (hK : IsCompact K) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ Kᶜ = 0} := by
  let f : K → E := Subtype.val
  have hf : IsClosedEmbedding f := IsClosedEmbedding.subtypeVal hK.isClosed
  have rf : range f = K := Subtype.range_val
  let F : FiniteMeasure K → FiniteMeasure E := fun μ ↦ μ.map f
  let T : Set (FiniteMeasure K) := {μ | μ.mass ≤ C}
  have : {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ Kᶜ = 0} = F '' T := by
    apply Subset.antisymm
    · intro μ hμ
      simp only [mem_image]
      refine ⟨μ.comap f, (FiniteMeasure.mass_comap_le _ _).trans hμ.1, ?_⟩
      ext s hs
      simp only [toMeasure_map, F]
      rw [Measure.map_apply measurable_subtype_coe hs]
      simp only [toMeasure_comap]
      rw [Measure.comap_apply _ (Subtype.val_injective), image_preimage_eq_inter_range]
      · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
        apply (null_iff_toMeasure_null (↑μ) (range f)ᶜ).mp
        rw [rf]
        exact hμ.2
      · exact fun t ht ↦ hf.measurableEmbedding.measurableSet_image' ht
      · exact hf.continuous.measurable hs
    · simp only [null_iff_toMeasure_null, image_subset_iff, preimage_setOf_eq, toMeasure_map,
        setOf_subset_setOf, F, T]
      intro μ hμ
      rw [Measure.map_apply hf.continuous.measurable hK.measurableSet.compl]
      refine ⟨(mass_map_le _ _).trans hμ, by simp [f]⟩
  rw [this]
  apply IsCompact.image _ (by fun_prop)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompact_setOf_finiteMeasure_le_of_compactSpace _ _

lemma isCompact_setOf_finiteMeasure_mass_eq_compl_isCompact_le {u : ℕ → ℝ≥0}
    {K : ℕ → Set E} (C : ℝ≥0) (hu : Tendsto u atTop (𝓝 0)) (hK : ∀ n, IsCompact (K n))
    (h : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : FiniteMeasure E | μ.mass = C ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by
  have : {μ : FiniteMeasure E | μ.mass = C ∧ ∀ n, μ (K n)ᶜ ≤ u n} =
    {μ | μ.mass ≤ C ∧ ∀ n, μ (K n)ᶜ ≤ u n} ∩ {μ | μ.mass = C} := by ext; grind
  rw [this]
  apply IsCompact.inter_right (isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le C hu hK h)
  exact isClosed_eq (by fun_prop) (by fun_prop)

lemma isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le {u : ℕ → ℝ≥0}
    {K : ℕ → Set E} (hu : Tendsto u atTop (𝓝 0)) (hK : ∀ n, IsCompact (K n))
    (h : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : ProbabilityMeasure E | ∀ n, μ (K n)ᶜ ≤ u n} := by
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding E).isCompact_iff.2
  have : ProbabilityMeasure.toFiniteMeasure '' {μ | ∀ (n : ℕ), μ (K n)ᶜ ≤ u n}
      = {μ : FiniteMeasure E | μ.mass = 1 ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by
    ext μ
    simp only [mem_image, mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨ν, hν, rfl⟩
      simpa using hν
    · rintro ⟨hμ, h'μ⟩
      let ν : ProbabilityMeasure E := ⟨μ, isProbabilityMeasure_iff_real.2 (by simpa using hμ)⟩
      have : ν.toFiniteMeasure = μ := by ext; rfl
      exact ⟨ν, by simpa [← this] using h'μ , this⟩
  rw [this]
  exact isCompact_setOf_finiteMeasure_mass_eq_compl_isCompact_le 1 hu hK h

lemma isCompact_closure_of_isTightMeasureSet {S : Set (ProbabilityMeasure E)}
    (hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}) :
    IsCompact (closure S) := by
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  have A n : ∃ (K : Set E), IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ u n := by
    rcases isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hS (u n)
      (by norm_cast; exact u_pos n) with ⟨K, K_comp, hK⟩
    refine ⟨K, K_comp, fun μ hμ ↦ ?_⟩
    have : (μ : Measure E) Kᶜ ≤ u n := hK _ ⟨μ, hμ, rfl⟩
    exact ENNReal.coe_le_coe.1 (by simpa using this)
  choose K K_comp hK using A
  let K' n := ⋃ i ∈ Iic n, K i
  have h'K : IsCompact {μ : ProbabilityMeasure E | ∀ n, μ (K' n)ᶜ ≤ u n} := by
    apply isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le u_lim
    · exact fun n ↦ (finite_Iic n).isCompact_biUnion (fun i hi ↦ K_comp i)
    · right
      simp only [Monotone, mem_Iic, le_eq_subset, iUnion_subset_iff, K']
      intro a b hab i hi
      apply subset_biUnion_of_mem
      exact hi.trans hab
  apply IsCompact.closure_of_subset h'K
  intro μ hμ n
  calc μ (K' n)ᶜ
  _ ≤ μ (K n)ᶜ := by
    gcongr
    simp only [mem_Iic, K']
    apply subset_biUnion_of_mem
    exact le_rfl (a := n)
  _ ≤ u n := by grind
