/-
Extracted from MeasureTheory/Measure/SeparableMeasure.lean
Genuine: 12 of 16 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Separable measure

The goal of this file is to give a sufficient condition on the measure space `(X, μ)` and the
`NormedAddCommGroup E` for the space `MeasureTheory.Lp E p μ` to have `SecondCountableTopology` when
`1 ≤ p < ∞`. To do so we define the notion of a `MeasureTheory.MeasureDense` family and a
separable measure (`MeasureTheory.IsSeparable`).
We prove that if `X` is `MeasurableSpace.CountablyGenerated` and `μ` is s-finite, then `μ`
is separable. We then prove that if `μ` is separable and `E` is second-countable,
then `Lp E p μ` is second-countable.

A family `𝒜` of subsets of `X` is said to be **measure-dense** if it contains only measurable sets
and can approximate any measurable set with finite measure, in the sense that
for any measurable set `s` such that `μ s ≠ ∞`, `μ (s ∆ t)` can be made
arbitrarily small when `t ∈ 𝒜`. We show below that such a family can be chosen to contain only
sets with finite measure.
The term "measure-dense" is justified by the fact that the approximating condition translates
to the usual notion of density in the metric space made by constant indicators of measurable sets
equipped with the `Lᵖ` norm.

A measure `μ` is **separable** if it admits a countable and measure-dense family of sets.
The term "separable" is justified by the fact that the definition translates to the usual notion
of separability in the metric space made by constant indicators equipped with the `Lᵖ` norm.

## Main definitions

* `MeasureTheory.Measure.MeasureDense μ 𝒜`: `𝒜` is a measure-dense family if it only contains
  measurable sets and if the following condition is satisfied: if `s` is measurable with finite
  measure, then for any `ε > 0` there exists `t ∈ 𝒜` such that `μ (s ∆ t) < ε`.
* `MeasureTheory.IsSeparable`: A measure is separable if there exists a countable and
  measure-dense family.

## Main statements

* `MeasureTheory.instSecondCountableLp`: If `μ` is separable, `E` is second-countable and
  `1 ≤ p < ∞` then `Lp E p μ` is second-countable. This is in particular true if `X` is countably
  generated and `μ` is s-finite.

## Implementation notes

Through the whole file we consider a measurable space `X` equipped with a measure `μ`, and also
a normed commutative group `E`. We also consider an extended non-negative real `p` such that
`1 ≤ p < ∞`. This is registered as instances via `one_le_p : Fact (1 ≤ p)` and
`p_ne_top : Fact (p ≠ ∞)`, so the properties are accessible via `one_le_p.elim` and `p_ne_top.elim`.

Through the whole file, when we write that an extended non-negative real is finite, it is always
written `≠ ∞` rather than `< ∞`. See `Ne.lt_top` and `ne_of_lt` to switch from one to the other.

## References

* [D. L. Cohn, *Measure Theory*][cohn2013measure]

## Tags

separable measure, measure-dense, Lp space, second-countable
-/

open MeasurableSpace Set ENNReal TopologicalSpace symmDiff Real

namespace MeasureTheory

variable {X E : Type*} [m : MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}

variable {p : ℝ≥0∞} [one_le_p : Fact (1 ≤ p)] [p_ne_top : Fact (p ≠ ∞)] {𝒜 : Set (Set X)}

section MeasureDense

/-! ### Definition of a measure-dense family, basic properties and sufficient conditions -/

structure Measure.MeasureDense (μ : Measure X) (𝒜 : Set (Set X)) : Prop where
  /-- Each set has to be measurable. -/
  measurable : ∀ s ∈ 𝒜, MeasurableSet s
  /-- Any measurable set can be approximated by sets in the family. -/
  approx : ∀ s, MeasurableSet s → μ s ≠ ∞ → ∀ ε : ℝ, 0 < ε → ∃ t ∈ 𝒜, μ (s ∆ t) < ENNReal.ofReal ε

theorem Measure.MeasureDense.nonempty (h𝒜 : μ.MeasureDense 𝒜) : 𝒜.Nonempty := by
  rcases h𝒜.approx ∅ MeasurableSet.empty (by simp) 1 (by simp) with ⟨t, ht, -⟩
  exact ⟨t, ht⟩

theorem Measure.MeasureDense.nonempty' (h𝒜 : μ.MeasureDense 𝒜) :
    {s | s ∈ 𝒜 ∧ μ s ≠ ∞}.Nonempty := by
  rcases h𝒜.approx ∅ MeasurableSet.empty (by simp) 1 (by simp) with ⟨t, ht, hμt⟩
  refine ⟨t, ht, ?_⟩
  convert ne_top_of_lt hμt
  rw [← bot_eq_empty, bot_symmDiff]

theorem Measure.MeasureDense.completion (h𝒜 : μ.MeasureDense 𝒜) : μ.completion.MeasureDense 𝒜 where
  measurable s hs := (h𝒜.measurable s hs).nullMeasurableSet
  approx s hs hμs ε ε_pos := by
    obtain ⟨t, ht, hμst⟩ :=
      h𝒜.approx (toMeasurable μ s) (measurableSet_toMeasurable μ s) (by simpa) ε ε_pos
    refine ⟨t, ht, ?_⟩
    convert hμst using 1
    rw [completion_apply]
    exact measure_congr <| ae_eq_set_symmDiff (NullMeasurableSet.toMeasurable_ae_eq hs).symm
      Filter.EventuallyEq.rfl

lemma Measure.MeasureDense.fin_meas_approx (h𝒜 : μ.MeasureDense 𝒜) {s : Set X}
    (ms : MeasurableSet s) (hμs : μ s ≠ ∞) (ε : ℝ) (ε_pos : 0 < ε) :
    ∃ t ∈ 𝒜, μ t ≠ ∞ ∧ μ (s ∆ t) < ENNReal.ofReal ε := by
  rcases h𝒜.approx s ms hμs ε ε_pos with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, (measure_ne_top_iff_of_symmDiff <| ne_top_of_lt ht).1 hμs, ht⟩

variable (p) in

theorem Measure.MeasureDense.indicatorConstLp_subset_closure (h𝒜 : μ.MeasureDense 𝒜) (c : E) :
    {indicatorConstLp p hs hμs c | (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)} ⊆
    closure {indicatorConstLp p (h𝒜.measurable s hs) hμs c |
      (s : Set X) (hs : s ∈ 𝒜) (hμs : μ s ≠ ∞)} := by
  obtain rfl | hc := eq_or_ne c 0
  · refine Subset.trans ?_ subset_closure
    rintro - ⟨s, ms, hμs, rfl⟩
    obtain ⟨t, ht, hμt⟩ := h𝒜.nonempty'
    refine ⟨t, ht, hμt, ?_⟩
    simp_rw [indicatorConstLp]
    simp
  · have p_pos : 0 < p := lt_of_lt_of_le (by simp) one_le_p.elim
    rintro - ⟨s, ms, hμs, rfl⟩
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    have aux : 0 < (ε / ‖c‖) ^ p.toReal := rpow_pos_of_pos (div_pos hε (norm_pos_iff.2 hc)) _
    obtain ⟨t, ht, hμt, hμst⟩ := h𝒜.fin_meas_approx ms hμs ((ε / ‖c‖) ^ p.toReal) aux
    refine ⟨indicatorConstLp p (h𝒜.measurable t ht) hμt c,
      ⟨t, ht, hμt, rfl⟩, ?_⟩
    rw [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp p_pos.ne.symm p_ne_top.elim]
    calc
      ‖c‖ * μ.real (s ∆ t) ^ (1 / p.toReal)
        < ‖c‖ * (ENNReal.ofReal ((ε / ‖c‖) ^ p.toReal)).toReal ^ (1 / p.toReal) := by
          have := toReal_pos p_pos.ne.symm p_ne_top.elim
          rw [measureReal_def]
          gcongr
          exact ofReal_ne_top
      _ = ε := by
        rw [toReal_ofReal (by positivity),
          one_div, Real.rpow_rpow_inv (by positivity) (toReal_pos p_pos.ne.symm p_ne_top.elim).ne',
          mul_div_cancel₀ _ (norm_ne_zero_iff.2 hc)]

theorem Measure.MeasureDense.fin_meas (h𝒜 : μ.MeasureDense 𝒜) :
    μ.MeasureDense {s | s ∈ 𝒜 ∧ μ s ≠ ∞} where
  measurable s h := h𝒜.measurable s h.1
  approx s ms hμs ε ε_pos := by
    rcases Measure.MeasureDense.fin_meas_approx h𝒜 ms hμs ε ε_pos with ⟨t, t_mem, hμt, hμst⟩
    exact ⟨t, ⟨t_mem, hμt⟩, hμst⟩

variable (μ) in

theorem Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite [IsFiniteMeasure μ]
    (h𝒜 : IsSetAlgebra 𝒜) (hgen : m = MeasurableSpace.generateFrom 𝒜) : μ.MeasureDense 𝒜 where
  measurable s hs := hgen ▸ measurableSet_generateFrom hs
  approx s ms := by
    -- We want to show that any measurable set can be approximated by sets in `𝒜`. To do so, it is
    -- enough to show that such sets constitute a `σ`-algebra containing `𝒜`. This is contained in
    -- the theorem `generateFrom_induction`.
    have : MeasurableSet s ∧ ∀ (ε : ℝ), 0 < ε → ∃ t ∈ 𝒜, μ.real (s ∆ t) < ε := by
      rw [hgen] at ms
      induction s, ms using generateFrom_induction with
      -- If `t ∈ 𝒜`, then `μ (t ∆ t) = 0` which is less than any `ε > 0`.
      | hC t t_mem _ =>
        exact ⟨hgen ▸ measurableSet_generateFrom t_mem, fun ε ε_pos ↦ ⟨t, t_mem, by simpa⟩⟩
      -- `∅ ∈ 𝒜` and `μ (∅ ∆ ∅) = 0` which is less than any `ε > 0`.
      | empty => exact ⟨MeasurableSet.empty, fun ε ε_pos ↦ ⟨∅, h𝒜.empty_mem, by simpa⟩⟩
      -- If `s` is measurable and `t ∈ 𝒜` such that `μ (s ∆ t) < ε`, then `tᶜ ∈ 𝒜` and
      -- `μ (sᶜ ∆ tᶜ) = μ (s ∆ t) < ε` so `sᶜ` can be approximated.
      | compl t _ ht =>
        refine ⟨ht.1.compl, fun ε ε_pos ↦ ?_⟩
        obtain ⟨u, u_mem, hμtcu⟩ := ht.2 ε ε_pos
        exact ⟨uᶜ, h𝒜.compl_mem u_mem, by rwa [compl_symmDiff_compl]⟩
      -- Let `(fₙ)` be a sequence of measurable sets and `ε > 0`.
      | iUnion f _ hf =>
        refine ⟨MeasurableSet.iUnion (fun n ↦ (hf n).1), fun ε ε_pos ↦ ?_⟩
        -- We have  `μ (⋃ n ≤ N, fₙ) ⟶ μ (⋃ n, fₙ)`.
        have := tendsto_measure_iUnion_accumulate (μ := μ) (f := f)
        rw [← tendsto_toReal_iff (fun _ ↦ measure_ne_top _ _) (measure_ne_top _ _)] at this
        -- So there exists `N` such that `μ (⋃ n, fₙ) - μ (⋃ n ≤ N, fₙ) < ε/2`.
        rcases Metric.tendsto_atTop.1 this (ε / 2) (by linarith [ε_pos]) with ⟨N, hN⟩
        -- For any `n ≤ N` there exists `gₙ ∈ 𝒜` such that `μ (fₙ ∆ gₙ) < ε/(2*(N+1))`.
        choose g g_mem hg using fun n ↦ (hf n).2 (ε / (2 * (N + 1))) (div_pos ε_pos (by linarith))
        -- Therefore we have
        -- `μ ((⋃ n, fₙ) ∆ (⋃ n ≤ N, gₙ))`
        --   `≤ μ ((⋃ n, fₙ) ∆ (⋃ n ≤ N, fₙ)) + μ ((⋃ n ≤ N, fₙ) ∆ (⋃ n ≤ N, gₙ))`
        --   `< ε/2 + ∑ n ≤ N, μ (fₙ ∆ gₙ)` (see `biSup_symmDiff_biSup_le`)
        --   `< ε/2 + (N+1)*ε/(2*(N+1)) = ε/2`.
        refine ⟨⋃ n ∈ Finset.range (N + 1), g n, h𝒜.biUnion_mem _ (fun i _ ↦ g_mem i), ?_⟩
        calc
          μ.real ((⋃ n, f n) ∆ (⋃ n ∈ (Finset.range (N + 1)), g n))
            ≤ (μ ((⋃ n, f n) \ ((⋃ n ∈ (Finset.range (N + 1)), f n)) ∪
              ((⋃ n ∈ (Finset.range (N + 1)), f n) ∆
              (⋃ n ∈ (Finset.range (N + 1)), g ↑n)))).toReal :=
                toReal_mono (measure_ne_top _ _)
                  (measure_mono <| symmDiff_of_ge (iUnion_subset <|
                  fun i ↦ iUnion_subset (fun _ ↦ subset_iUnion f i)) ▸ symmDiff_triangle ..)
          _ ≤ (μ ((⋃ n, f n) \
              ((⋃ n ∈ (Finset.range (N + 1)), f n)))).toReal +
              (μ ((⋃ n ∈ (Finset.range (N + 1)), f n) ∆
              (⋃ n ∈ (Finset.range (N + 1)), g ↑n))).toReal := by
                rw [← toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
                exact toReal_mono (add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) <|
                  measure_union_le _ _
          _ < ε := by
                rw [← add_halves ε]
                apply _root_.add_lt_add
                · rw [measure_diff (h_fin := measure_ne_top _ _),
                    toReal_sub_of_le (ha := measure_ne_top _ _)]
                  · apply lt_of_le_of_lt (sub_le_dist ..)
                    simp only [Finset.mem_range, Nat.lt_add_one_iff]
                    exact (dist_comm (α := ℝ) .. ▸ hN N (le_refl N))
                  · exact measure_mono <| iUnion_subset <|
                      fun i ↦ iUnion_subset fun _ ↦ subset_iUnion f i
                  · exact iUnion_subset <| fun i ↦ iUnion_subset (fun _ ↦ subset_iUnion f i)
                  · exact MeasurableSet.biUnion (countable_coe_iff.1 inferInstance)
                      (fun n _ ↦ (hf n).1.nullMeasurableSet)
                · calc
                    (μ ((⋃ n ∈ (Finset.range (N + 1)), f n) ∆
                    (⋃ n ∈ (Finset.range (N + 1)), g ↑n))).toReal
                      ≤ μ.real (⋃ n ∈ (Finset.range (N + 1)), f n ∆ g n) :=
                          toReal_mono (measure_ne_top _ _) (measure_mono biSup_symmDiff_biSup_le)
                    _ ≤ ∑ n ∈ Finset.range (N + 1), μ.real (f n ∆ g n) := by
                          simp_rw [measureReal_def, ← toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
                          exact toReal_mono (ne_of_lt <| sum_lt_top.2 fun _ _ ↦ measure_lt_top μ _)
                            (measure_biUnion_finset_le _ _)
                    _ < ∑ n ∈ Finset.range (N + 1), (ε / (2 * (N + 1))) :=
                          Finset.sum_lt_sum (fun i _ ↦ le_of_lt (hg i)) ⟨0, by simp, hg 0⟩
                    _ ≤ ε / 2 := by
                          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                            Nat.cast_add, Nat.cast_one]
                          rw [div_mul_eq_div_mul_one_div, ← mul_assoc, mul_comm ((N : ℝ) + 1),
                            mul_assoc]
                          exact mul_le_of_le_one_right (by linarith [ε_pos]) <|
                            le_of_eq <| mul_one_div_cancel <| Nat.cast_add_one_ne_zero _
    rintro - ε ε_pos
    rcases this.2 ε ε_pos with ⟨t, t_mem, hμst⟩
    exact ⟨t, t_mem, (lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 hμst⟩

theorem Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite (h𝒜 : IsSetAlgebra 𝒜)
    (S : μ.FiniteSpanningSetsIn 𝒜) (hgen : m = MeasurableSpace.generateFrom 𝒜) :
    μ.MeasureDense 𝒜 where
  measurable s hs := hgen ▸ measurableSet_generateFrom hs
  approx s ms hμs ε ε_pos := by
    -- We use partial unions of (Sₙ) to get a monotone family spanning `X`.
    let T := accumulate S.set
    have T_mem (n) : T n ∈ 𝒜 := by
      simpa using h𝒜.biUnion_mem {k | k ≤ n}.toFinset (fun k _ ↦ S.set_mem k)
    have T_finite (n) : μ (T n) < ∞ := by
      simpa using measure_biUnion_lt_top {k | k ≤ n}.toFinset.finite_toSet
        (fun k _ ↦ S.finite k)
    have T_spanning : ⋃ n, T n = univ := S.spanning ▸ iUnion_accumulate
    -- We use the fact that we already know this is true for finite measures. As `⋃ n, T n = X`,
    -- we have that `μ ((T n) ∩ s) ⟶ μ s`.
    have mono : Monotone (fun n ↦ (T n) ∩ s) := fun m n hmn ↦ inter_subset_inter_left s
        (biUnion_subset_biUnion_left fun k hkm ↦ Nat.le_trans hkm hmn)
    have := tendsto_measure_iUnion_atTop (μ := μ) mono
    rw [← tendsto_toReal_iff] at this
    · -- We can therefore choose `N` such that `μ s - μ ((S N) ∩ s) < ε/2`.
      rcases Metric.tendsto_atTop.1 this (ε / 2) (by linarith [ε_pos]) with ⟨N, hN⟩
      have : Fact (μ (T N) < ∞) := Fact.mk <| T_finite N
      -- Then we can apply the previous result to the measure `μ ((S N) ∩ •)`.
      -- There exists `t ∈ 𝒜` such that `μ ((S N) ∩ (s ∆ t)) < ε/2`.
      rcases (Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
        (μ.restrict (T N)) h𝒜 hgen).approx s ms
        (ne_of_lt (lt_of_le_of_lt (μ.restrict_apply_le _ s) hμs.lt_top))
        (ε / 2) (by linarith [ε_pos])
        with ⟨t, t_mem, ht⟩
      -- We can then use `t ∩ (S N)`, because `S N ∈ 𝒜` by hypothesis.
      -- `μ (s ∆ (t ∩ S N))`
      --   `≤ μ (s ∆ (s ∩ S N)) + μ ((s ∩ S N) ∆ (t ∩ S N))`
      --   `= μ s - μ (s ∩ S N) + μ (s ∆ t) ∩ S N) < ε`.
      refine ⟨t ∩ T N, h𝒜.inter_mem t_mem (T_mem N), ?_⟩
      calc
        μ (s ∆ (t ∩ T N))
          ≤ μ (s \ (s ∩ T N)) + μ ((s ∆ t) ∩ T N) := by
              rw [← symmDiff_of_le (inter_subset_left ..), symmDiff_comm _ s,
                inter_symmDiff_distrib_right]
              exact measure_symmDiff_le _ _ _
        _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
              apply ENNReal.add_lt_add
              · rw [measure_diff
                    (inter_subset_left ..)
                    (ms.inter (hgen ▸ measurableSet_generateFrom (T_mem N))).nullMeasurableSet
                    (ne_top_of_le_ne_top hμs (measure_mono (inter_subset_left ..))),
                  lt_ofReal_iff_toReal_lt (sub_ne_top hμs),
                  toReal_sub_of_le (measure_mono (inter_subset_left ..)) hμs]
                apply lt_of_le_of_lt (sub_le_dist ..)
                nth_rw 1 [← univ_inter s]
                rw [inter_comm s, dist_comm, ← T_spanning, iUnion_inter _ T]
                apply hN N (le_refl _)
              · rwa [← μ.restrict_apply' (hgen ▸ measurableSet_generateFrom (T_mem N))]
        _ = ENNReal.ofReal ε := by
              rw [← ofReal_add (by linarith [ε_pos]) (by linarith [ε_pos]), add_halves]
    · exact fun n ↦ ne_top_of_le_ne_top hμs (measure_mono (inter_subset_right ..))
    · exact ne_top_of_le_ne_top hμs
        (measure_mono (iUnion_subset (fun i ↦ inter_subset_right ..)))

end MeasureDense

section IsSeparable

/-! ### Definition of a separable measure space, sufficient condition -/

class IsSeparable (μ : Measure X) : Prop where
  exists_countable_measureDense : ∃ 𝒜, 𝒜.Countable ∧ μ.MeasureDense 𝒜

variable (μ)

theorem exists_countable_measureDense [IsSeparable μ] :
    ∃ 𝒜, 𝒜.Countable ∧ μ.MeasureDense 𝒜 :=
  IsSeparable.exists_countable_measureDense

theorem isSeparable_of_sigmaFinite [CountablyGenerated X] [SigmaFinite μ] :
    IsSeparable μ where
  exists_countable_measureDense := by
    have h := countable_countableGeneratingSet (α := X)
    have hgen := generateFrom_countableGeneratingSet (α := X)
    let 𝒜 := (countableGeneratingSet X) ∪ {μ.toFiniteSpanningSetsIn.set n | n : ℕ}
    have count_𝒜 : 𝒜.Countable :=
      countable_union.2 ⟨h, countable_iff_exists_subset_range.2
        ⟨μ.toFiniteSpanningSetsIn.set, fun _ hx ↦ hx⟩⟩
    refine ⟨generateSetAlgebra 𝒜, countable_generateSetAlgebra count_𝒜,
      Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite isSetAlgebra_generateSetAlgebra
      { set := μ.toFiniteSpanningSetsIn.set
        set_mem := fun n ↦ self_subset_generateSetAlgebra (𝒜 := 𝒜) <| Or.inr ⟨n, rfl⟩
        finite := μ.toFiniteSpanningSetsIn.finite
        spanning := μ.toFiniteSpanningSetsIn.spanning }
      (le_antisymm ?_ (generateFrom_le (fun s hs ↦ ?_)))⟩
    · rw [← hgen]
      exact generateFrom_mono <| le_trans self_subset_generateSetAlgebra <|
        generateSetAlgebra_mono <| subset_union_left ..
    · induction hs with
      | base t t_mem =>
        rcases t_mem with t_mem | ⟨n, rfl⟩
        · exact hgen ▸ measurableSet_generateFrom t_mem
        · exact μ.toFiniteSpanningSetsIn.set_mem n
      | empty => exact MeasurableSet.empty
      | compl t _ t_mem => exact MeasurableSet.compl t_mem
      | union t u _ _ t_mem u_mem => exact MeasurableSet.union t_mem u_mem

-- INSTANCE (free from Core): [CountablyGenerated

-- INSTANCE (free from Core): [hμ

end IsSeparable

section SecondCountableLp

/-! ### A sufficient condition for $L^p$ spaces to be second-countable -/

-- INSTANCE (free from Core): Lp.SecondCountableTopology

end SecondCountableLp

end MeasureTheory
