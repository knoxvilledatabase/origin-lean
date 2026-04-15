/-
Extracted from MeasureTheory/OuterMeasure/OfFunction.lean
Genuine: 18 of 19 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Outer measures from functions

Given an arbitrary function `m : Set α → ℝ≥0∞` that sends `∅` to `0` we can define an outer
measure on `α` that on `s` is defined to be the infimum of `∑ᵢ, m (sᵢ)` for all collections of sets
`sᵢ` that cover `s`. This is the unique maximal outer measure that is at most the given function.

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `OuterMeasure.boundedBy` is the greatest outer measure that is at most the given function.
  If you know that the given function sends `∅` to `0`, then `OuterMeasure.ofFunction` is a
  special case.
* `sInf_eq_boundedBy_sInfGen` is a characterization of the infimum of outer measures.

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

outer measure, Carathéodory-measurable, Carathéodory's criterion

-/

assert_not_exists Module.Basis

noncomputable section

open Set Function Filter

open scoped NNReal Topology ENNReal

namespace MeasureTheory

namespace OuterMeasure

section OfFunction

variable {α : Type*}

protected def ofFunction (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0) : OuterMeasure α :=
  let μ s := ⨅ (f : ℕ → Set α) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i)
  { measureOf := μ
    empty :=
      le_antisymm
        ((iInf_le_of_le fun _ => ∅) <| iInf_le_of_le (empty_subset _) <| by simp [m_empty])
        (zero_le _)
    mono := fun {_ _} hs => iInf_mono fun _ => iInf_mono' fun hb => ⟨hs.trans hb, le_rfl⟩
    iUnion_nat := fun s _ =>
      ENNReal.le_of_forall_pos_le_add <| by
        intro ε hε (hb : (∑' i, μ (s i)) < ∞)
        rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 hε).ne' ℕ with ⟨ε', hε', hl⟩
        grw [← hl]
        rw [← ENNReal.tsum_add]
        choose f hf using
          show ∀ i, ∃ f : ℕ → Set α, (s i ⊆ ⋃ i, f i) ∧ (∑' i, m (f i)) < μ (s i) + ε' i by
            intro i
            have : μ (s i) < μ (s i) + ε' i :=
              ENNReal.lt_add_right (ne_top_of_le_ne_top hb.ne <| ENNReal.le_tsum _)
                (by simpa using (hε' i).ne')
            rcases iInf_lt_iff.mp this with ⟨t, ht⟩
            exists t
            contrapose! ht
            exact le_iInf ht
        refine le_trans ?_ (ENNReal.tsum_le_tsum fun i => le_of_lt (hf i).2)
        rw [← ENNReal.tsum_prod, ← Nat.pairEquiv.symm.tsum_eq]
        refine iInf_le_of_le _ (iInf_le _ ?_)
        apply iUnion_subset
        intro i
        apply Subset.trans (hf i).1
        apply iUnion_subset
        simp only [Nat.pairEquiv_symm_apply]
        rw [iUnion_unpair]
        intro j
        apply subset_iUnion₂ i }

variable (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0)

theorem ofFunction_eq_iInf_mem {P : Set α → Prop} (m_top : ∀ s, ¬ P s → m s = ∞) (s : Set α) :
    OuterMeasure.ofFunction m m_empty s =
      ⨅ (t : ℕ → Set α) (_ : ∀ i, P (t i)) (_ : s ⊆ ⋃ i, t i), ∑' i, m (t i) := by
  rw [OuterMeasure.ofFunction_apply]
  apply le_antisymm
  · exact le_iInf fun t ↦ le_iInf fun _ ↦ le_iInf fun h ↦ iInf₂_le _ (by exact h)
  · simp_rw [le_iInf_iff]
    refine fun t ht_subset ↦ iInf_le_of_le t ?_
    by_cases ht : ∀ i, P (t i)
    · exact iInf_le_of_le ht (iInf_le_of_le ht_subset le_rfl)
    · simp only [ht, not_false_eq_true, iInf_neg, top_le_iff]
      push Not at ht
      obtain ⟨i, hti_notMem⟩ := ht
      have hfi_top : m (t i) = ∞ := m_top _ hti_notMem
      exact ENNReal.tsum_eq_top_of_eq_top ⟨i, hfi_top⟩

variable {m m_empty}

theorem ofFunction_le (s : Set α) : OuterMeasure.ofFunction m m_empty s ≤ m s :=
  let f : ℕ → Set α := fun i => Nat.casesOn i s fun _ => ∅
  iInf_le_of_le f <|
    iInf_le_of_le (subset_iUnion f 0) <|
      le_of_eq <| tsum_eq_single 0 <| by
        rintro (_ | i)
        · simp
        · simp [f, m_empty]

theorem ofFunction_eq (s : Set α) (m_mono : ∀ ⦃t : Set α⦄, s ⊆ t → m s ≤ m t)
    (m_subadd : ∀ s : ℕ → Set α, m (⋃ i, s i) ≤ ∑' i, m (s i)) :
    OuterMeasure.ofFunction m m_empty s = m s :=
  le_antisymm (ofFunction_le s) <|
    le_iInf fun f => le_iInf fun hf => le_trans (m_mono hf) (m_subadd f)

theorem le_ofFunction {μ : OuterMeasure α} :
    μ ≤ OuterMeasure.ofFunction m m_empty ↔ ∀ s, μ s ≤ m s :=
  ⟨fun H s => le_trans (H s) (ofFunction_le s), fun H _ =>
    le_iInf fun f =>
      le_iInf fun hs =>
        le_trans (μ.mono hs) <| le_trans (measure_iUnion_le f) <| ENNReal.tsum_le_tsum fun _ => H _⟩

theorem isGreatest_ofFunction :
    IsGreatest { μ : OuterMeasure α | ∀ s, μ s ≤ m s } (OuterMeasure.ofFunction m m_empty) :=
  ⟨fun _ => ofFunction_le _, fun _ => le_ofFunction.2⟩

theorem ofFunction_eq_sSup : OuterMeasure.ofFunction m m_empty = sSup { μ | ∀ s, μ s ≤ m s } :=
  (@isGreatest_ofFunction α m m_empty).isLUB.sSup_eq.symm

theorem ofFunction_union_of_top_of_nonempty_inter {s t : Set α}
    (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → m u = ∞) :
    OuterMeasure.ofFunction m m_empty (s ∪ t) =
      OuterMeasure.ofFunction m m_empty s + OuterMeasure.ofFunction m m_empty t := by
  refine le_antisymm (measure_union_le _ _) (le_iInf₂ fun f hf ↦ ?_)
  set μ := OuterMeasure.ofFunction m m_empty
  rcases Classical.em (∃ i, (s ∩ f i).Nonempty ∧ (t ∩ f i).Nonempty) with (⟨i, hs, ht⟩ | he)
  · calc
      μ s + μ t ≤ ∞ := le_top
      _ = m (f i) := (h (f i) hs ht).symm
      _ ≤ ∑' i, m (f i) := ENNReal.le_tsum i
  set I := fun s => { i : ℕ | (s ∩ f i).Nonempty }
  have hd : Disjoint (I s) (I t) := disjoint_iff_inf_le.mpr fun i hi => he ⟨i, hi⟩
  have hI : ∀ u ⊆ s ∪ t, μ u ≤ ∑' i : I u, μ (f i) := fun u hu =>
    calc
      μ u ≤ μ (⋃ i : I u, f i) :=
        μ.mono fun x hx =>
          let ⟨i, hi⟩ := mem_iUnion.1 (hf (hu hx))
          mem_iUnion.2 ⟨⟨i, ⟨x, hx, hi⟩⟩, hi⟩
      _ ≤ ∑' i : I u, μ (f i) := measure_iUnion_le _
  calc
    μ s + μ t ≤ (∑' i : I s, μ (f i)) + ∑' i : I t, μ (f i) :=
      add_le_add (hI _ subset_union_left) (hI _ subset_union_right)
    _ = ∑' i : ↑(I s ∪ I t), μ (f i) :=
      (ENNReal.summable.tsum_union_disjoint (f := fun i => μ (f i)) hd ENNReal.summable).symm
    _ ≤ ∑' i, μ (f i) :=
      (ENNReal.summable.tsum_le_tsum_of_inj (↑) Subtype.coe_injective (fun _ _ => zero_le _)
        (fun _ => le_rfl) ENNReal.summable)
    _ ≤ ∑' i, m (f i) := ENNReal.tsum_le_tsum fun i => ofFunction_le _

theorem comap_ofFunction {β} (f : β → α) (h : Monotone m ∨ Surjective f) :
    comap f (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun s => m (f '' s)) (by simp; simp [m_empty]) := by
  refine le_antisymm (le_ofFunction.2 fun s => ?_) fun s => ?_
  · rw [comap_apply]
    apply ofFunction_le
  · rw [comap_apply, ofFunction_apply, ofFunction_apply]
    refine iInf_mono' fun t => ⟨fun k => f ⁻¹' t k, ?_⟩
    refine iInf_mono' fun ht => ?_
    rw [Set.image_subset_iff, preimage_iUnion] at ht
    refine ⟨ht, ENNReal.tsum_le_tsum fun n => ?_⟩
    rcases h with hl | hr
    exacts [hl (image_preimage_subset _ _), (congr_arg m (hr.image_preimage (t n))).le]

theorem map_ofFunction_le {β} (f : α → β) :
    map f (OuterMeasure.ofFunction m m_empty) ≤
      OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty :=
  le_ofFunction.2 fun s => by
    rw [map_apply]
    apply ofFunction_le

theorem map_ofFunction {β} {f : α → β} (hf : Injective f) :
    map f (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty := by
  refine (map_ofFunction_le _).antisymm fun s => ?_
  simp only [ofFunction_apply, map_apply, le_iInf_iff]
  intro t ht
  refine iInf_le_of_le (fun n => (range f)ᶜ ∪ f '' t n) (iInf_le_of_le ?_ ?_)
  · rw [← union_iUnion, ← inter_subset, ← image_preimage_eq_inter_range, ← image_iUnion]
    exact image_mono ht
  · refine ENNReal.tsum_le_tsum fun n => le_of_eq ?_
    simp [hf.preimage_image]

theorem restrict_ofFunction (s : Set α) (hm : Monotone m) :
    restrict s (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun t => m (t ∩ s)) (by simp; simp [m_empty]) := by
      rw [restrict]
      simp only [inter_comm _ s, LinearMap.comp_apply]
      rw [comap_ofFunction _ (Or.inl hm)]
      simp only [map_ofFunction Subtype.coe_injective, Subtype.image_preimage_coe]

theorem smul_ofFunction {c : ℝ≥0∞} (hc : c ≠ ∞) : c • OuterMeasure.ofFunction m m_empty =
    OuterMeasure.ofFunction (c • m) (by simp [m_empty]) := by
  ext1 s
  haveI : Nonempty { t : ℕ → Set α // s ⊆ ⋃ i, t i } := ⟨⟨fun _ => s, subset_iUnion (fun _ => s) 0⟩⟩
  simp only [smul_apply, ofFunction_apply, ENNReal.tsum_mul_left, Pi.smul_apply, smul_eq_mul,
  iInf_subtype']
  rw [ENNReal.mul_iInf fun h => (hc h).elim]

end OfFunction

section BoundedBy

variable {α : Type*} (m : Set α → ℝ≥0∞)

def boundedBy : OuterMeasure α :=
  OuterMeasure.ofFunction (fun s => ⨆ _ : s.Nonempty, m s) (by simp [Set.not_nonempty_empty])

variable {m}

theorem boundedBy_le (s : Set α) : boundedBy m s ≤ m s :=
  (ofFunction_le _).trans iSup_const_le

theorem boundedBy_eq_ofFunction (m_empty : m ∅ = 0) (s : Set α) :
    boundedBy m s = OuterMeasure.ofFunction m m_empty s := by
  have : (fun s : Set α => ⨆ _ : s.Nonempty, m s) = m := by
    ext1 t
    rcases t.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty, m_empty]
  simp [boundedBy, this]

theorem boundedBy_apply (s : Set α) :
    boundedBy m s = ⨅ (t : ℕ → Set α) (_ : s ⊆ iUnion t),
                      ∑' n, ⨆ _ : (t n).Nonempty, m (t n) := by
  simp [boundedBy, ofFunction_apply]

theorem boundedBy_eq (s : Set α) (m_empty : m ∅ = 0) (m_mono : ∀ ⦃t : Set α⦄, s ⊆ t → m s ≤ m t)
    (m_subadd : ∀ s : ℕ → Set α, m (⋃ i, s i) ≤ ∑' i, m (s i)) : boundedBy m s = m s := by
  rw [boundedBy_eq_ofFunction m_empty, ofFunction_eq s m_mono m_subadd]
