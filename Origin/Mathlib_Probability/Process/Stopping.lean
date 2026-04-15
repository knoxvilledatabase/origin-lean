/-
Extracted from Probability/Process/Stopping.lean
Genuine: 28 of 29 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Stopping times, stopped processes and stopped values

Definition and properties of stopping times.

## Main definitions

* `MeasureTheory.IsStoppingTime`: a stopping time with respect to some filtration `f` on a
  measurable space `Ω` is a function `τ : Ω → WithTop ι` such that for all `i : ι`,
  the preimage of `{j | j ≤ i}` along `τ` is `f i`-measurable
* `MeasureTheory.IsStoppingTime.measurableSpace`: the σ-algebra associated with a stopping time

## Main results

* `ProgMeasurable.stoppedProcess`: the stopped process of a progressively measurable process is
  progressively measurable.
* `memLp_stoppedProcess`: if a process belongs to `ℒp` at every time in `ℕ`, then its stopped
  process belongs to `ℒp` as well.

## Implementation notes

For a filtration on a type `ι`, we define stopping times as functions from the measurable space `Ω`
to `WithTop ι`, which allows stopping times that can take an infinite value, represented by
`⊤ : WithTop ι`.

This means that if we have a process `X : ι → Ω → β` and a stopping time `τ : Ω → WithTop ι`, then
to consider the value of `X` at the stopping time `τ ω`, we need to write `X (τ ω).untopA ω`,
in which `(τ ω).untopA` is the value of `τ ω` in `ι` if `τ ω ≠ ⊤` and some arbitrary value if
`τ ω = ⊤`.

While indexing would be more convenient if we defined stopping times as functions from `Ω` to `ι`,
this would prevent us from using stopping times as in standard mathematical literature, where a
typical example of stopping time is the first time an event occurs, which may never happen.
Consider for example the first time a coin lands heads when flipping it infinitely many times:
this is almost surely finite, but possibly infinite. We could also not use a function `Ω → ι` with
arbitrary value for the infinite case, because this would be incompatible with the stopping time
property.

## Tags

stopping time, stochastic process

-/

open Filter Order TopologicalSpace WithTop

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

/-! ### Stopping times -/

def IsStoppingTime [Preorder ι] (f : Filtration ι m) (τ : Ω → WithTop ι) :=
  ∀ i : ι, MeasurableSet[f i] <| {ω | τ ω ≤ i}

theorem isStoppingTime_const [Preorder ι] (f : Filtration ι m) (i : ι) :
    IsStoppingTime f fun _ => i := fun j => by simp only [MeasurableSet.const]

section MeasurableSet

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}

protected theorem IsStoppingTime.measurableSet_le (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω ≤ i} :=
  hτ i

theorem IsStoppingTime.measurableSet_lt_of_pred [PredOrder ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} := by
  by_cases hi_min : IsMin i
  · suffices {ω : Ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [isMin_iff_forall_not_lt] at hi_min
    cases τ ω with
    | top => simp
    | coe t => exact mod_cast hi_min t
  have : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iic (pred i : ι) := by
    ext ω
    push _ ∈ _
    cases τ ω with
    | top => simp
    | coe t =>
      simp only [coe_lt_coe, coe_le_coe]
      rw [le_pred_iff_of_not_isMin hi_min]
  rw [this]
  exact f.mono (pred_le i) _ (hτ.measurableSet_le <| pred i)

end Preorder

section CountableStoppingTime

namespace IsStoppingTime

variable [PartialOrder ι] {τ : Ω → WithTop ι} {f : Filtration ι m}

protected theorem measurableSet_eq_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) : MeasurableSet[f i] {ω | τ ω = i} := by
  have : {ω | τ ω = i} = {ω | τ ω ≤ i} \ ⋃ (j ∈ Set.range τ) (_ : j < i), {ω | τ ω ≤ j} := by
    ext1 a
    simp only [Set.mem_setOf_eq, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_diff, Set.mem_iUnion, exists_prop, not_exists, not_and]
    constructor <;> intro h
    · simp only [h, lt_iff_le_not_ge, le_refl, and_imp, imp_self, imp_true_iff, and_self_iff]
    · exact h.1.eq_or_lt.resolve_right fun h_lt => h.2 a h_lt le_rfl
  rw [this]
  refine (hτ.measurableSet_le i).diff ?_
  refine MeasurableSet.biUnion h_countable fun j _ => ?_
  classical
  rw [Set.iUnion_eq_if]
  split_ifs with hji
  · lift j to ι using (ne_top_of_lt hji)
    exact f.mono (mod_cast hji.le) _ (hτ.measurableSet_le j)
  · exact @MeasurableSet.empty _ (f i)

protected theorem measurableSet_eq_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω = i} :=
  hτ.measurableSet_eq_of_countable_range (Set.to_countable _) i

protected theorem measurableSet_lt_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) : MeasurableSet[f i] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i} := by ext1 ω; simp [lt_iff_le_and_ne]
  rw [this]
  exact (hτ.measurableSet_le i).diff (hτ.measurableSet_eq_of_countable_range h_countable i)

protected theorem measurableSet_lt_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} :=
  hτ.measurableSet_lt_of_countable_range (Set.to_countable _) i

protected theorem measurableSet_ge_of_countable_range {ι} [LinearOrder ι] {τ : Ω → WithTop ι}
    {f : Filtration ι m} (hτ : IsStoppingTime f τ) (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt_of_countable_range h_countable i).compl

protected theorem measurableSet_ge_of_countable {ι} [LinearOrder ι] {τ : Ω → WithTop ι}
    {f : Filtration ι m} [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} :=
  hτ.measurableSet_ge_of_countable_range (Set.to_countable _) i

end IsStoppingTime

end CountableStoppingTime

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}

theorem IsStoppingTime.measurableSet_gt (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i < τ ω} := by
  have : {ω | i < τ ω} = {ω | τ ω ≤ i}ᶜ := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  rw [this]
  exact (hτ.measurableSet_le i).compl

section TopologicalSpace

variable [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]

theorem IsStoppingTime.measurableSet_lt_of_isLUB (hτ : IsStoppingTime f τ) (i : ι)
    (h_lub : IsLUB (Set.Iio i) i) : MeasurableSet[f i] {ω | τ ω < i} := by
  by_cases hi_min : IsMin i
  · suffices {ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    cases τ ω with
    | top => simp
    | coe t => norm_cast; exact isMin_iff_forall_not_lt.mp hi_min t
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ :
      ∃ seq : ℕ → ι, Monotone seq ∧ (∀ j, seq j ≤ i) ∧ Tendsto seq atTop (𝓝 i) ∧ ∀ j, seq j < i :=
    h_lub.exists_seq_monotone_tendsto (not_isMin_iff.mp hi_min)
  have h_Iio_eq_Union : Set.Iio (i : WithTop ι) = ⋃ j, {k : WithTop ι | k ≤ seq j} := by
    ext1 k
    push _ ∈ _
    refine ⟨fun hk_lt_i => ?_, fun h_exists_k_le_seq => ?_⟩
    · rw [tendsto_atTop'] at h_tendsto
      cases k with
      | top => simp at hk_lt_i
      | coe k =>
        norm_cast at hk_lt_i ⊢
        have h_nhds : Set.Ici k ∈ 𝓝 i :=
          mem_nhds_iff.mpr ⟨Set.Ioi k, Set.Ioi_subset_Ici le_rfl, isOpen_Ioi, hk_lt_i⟩
        obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ b : ℕ, b ≥ a → k ≤ seq b := h_tendsto (Set.Ici k) h_nhds
        exact ⟨a, ha a le_rfl⟩
    · obtain ⟨j, hk_seq_j⟩ := h_exists_k_le_seq
      exact hk_seq_j.trans_lt (mod_cast h_bound j)
  have h_lt_eq_preimage : {ω | τ ω < i} = τ ⁻¹' Set.Iio i := by
    ext1 ω; push _ ∈ _; rfl
  rw [h_lt_eq_preimage, h_Iio_eq_Union]
  simp only [Set.preimage_iUnion, Set.preimage_setOf_eq]
  exact MeasurableSet.iUnion fun n => f.mono (h_bound n).le _ (hτ.measurableSet_le (seq n))

theorem IsStoppingTime.measurableSet_ge (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i ≤ τ ω} := by
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt i).compl

theorem IsStoppingTime.measurableSet_eq (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω = i} := by
  have : {ω | τ ω = i} = {ω | τ ω ≤ i} ∩ {ω | τ ω ≥ i} := by
    ext1 ω; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, le_antisymm_iff]
  rw [this]
  exact (hτ.measurableSet_le i).inter (hτ.measurableSet_ge i)

theorem IsStoppingTime.measurableSet_eq_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    MeasurableSet[f j] {ω | τ ω = i} :=
  f.mono hle _ <| hτ.measurableSet_eq i

theorem IsStoppingTime.measurableSet_lt_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    MeasurableSet[f j] {ω | τ ω < i} :=
  f.mono hle _ <| hτ.measurableSet_lt i

end TopologicalSpace

end LinearOrder

section Countable

theorem isStoppingTime_of_measurableSet_eq [Preorder ι] [Countable ι] {f : Filtration ι m}
    {τ : Ω → WithTop ι} (hτ : ∀ i, MeasurableSet[f i] {ω | τ ω = i}) : IsStoppingTime f τ := by
  intro i
  have h_eq_iUnion : {ω | τ ω ≤ i} = ⋃ k ≤ i, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp
  rw [h_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun k hk => ?_
  exact f.mono hk _ (hτ k)

end Countable

section IsRightContinuous

open Filtration

variable [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] {f : Filtration ι m} {τ : Ω → WithTop ι}

set_option backward.isDefEq.respectTransparency false in

lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous' [hf : f.IsRightContinuous]
    (hτ1 : ∀ i, MeasurableSet[f i] {ω | τ ω < i})
    (hτ2 : ∀ i, 𝓝[>] i = ⊥ → MeasurableSet[f i] {ω | τ ω = i}) :
    IsStoppingTime f τ := by
  intro t
  by_cases ht : 𝓝[>] t = ⊥
  · have h_eq : {ω | τ ω ≤ t} = {ω | τ ω < t} ∪ {ω | τ ω = t} := by ext; grind
    rw [h_eq]
    exact (hτ1 t).union (hτ2 t ht)
  have : (𝓝[>] t).NeBot := ⟨ht⟩
  -- now `t` is a limit point on the right
  obtain ⟨s, hs_gt, hs_tendsto⟩ : ∃ s : ℕ → ι, (∀ n, t < s n) ∧ Tendsto s atTop (𝓝 t) := by
    have h_freq : ∃ᶠ x in 𝓝[>] t, t < x :=
      Eventually.frequently <| eventually_nhdsWithin_of_forall fun _ hx ↦ hx
    have := exists_seq_forall_of_frequently h_freq
    simp_rw [tendsto_nhdsWithin_iff] at this
    obtain ⟨s, ⟨hs_tendsto, _⟩, hs_gt⟩ := this
    exact ⟨s, hs_gt, hs_tendsto⟩
  have h_exists_lt (u : ι) (hu : t < u) : ∃ i, s i < u :=
    Eventually.exists (f := atTop) (hs_tendsto.eventually_lt_const hu)
  have h_exists_lt' (u : WithTop ι) (hu : t < u) : ∃ i, s i < u := by
    refine Eventually.exists (f := atTop) ?_
    have hs_tendsto' : Tendsto (fun n ↦ (s n : WithTop ι)) atTop (𝓝 (t : WithTop ι)) :=
      WithTop.continuous_coe.continuousAt.tendsto.comp hs_tendsto
    exact hs_tendsto'.eventually_lt_const hu
  -- we write `{τ ≤ t}` as a countable intersection of `{τ < s n}`
  have h_eq_iInter : {ω | τ ω ≤ t} = ⋂ m, {ω | τ ω < s m} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h_le m ↦ h_le.trans_lt (mod_cast (hs_gt m)), fun h_lt ↦ ?_⟩
    refine le_of_forall_gt fun u hu ↦ ?_
    obtain ⟨i, hi⟩ : ∃ i, s i < u := h_exists_lt' u hu
    exact (h_lt i).trans hi
  rw [h_eq_iInter]
  have h𝓕_eq_iInf : f t = ⨅ m, f (s m) := by
    nth_rw 1 [← hf.eq, Filtration.rightCont_eq_of_neBot_nhdsGT]
    refine le_antisymm ?_ ?_
    · simp only [gt_iff_lt, le_iInf_iff]
      exact fun i ↦ iInf₂_le (s i) (hs_gt i)
    · simp only [gt_iff_lt, le_iInf_iff]
      intro i hti
      obtain ⟨m, hm⟩ := h_exists_lt i hti
      exact (iInf_le _ m).trans (f.mono hm.le)
  rw [h𝓕_eq_iInf]
  simp only [MeasurableSpace.measurableSet_sInf, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff]
  intro k
  have h_eq_k : ⋂ m, {ω | τ ω < s m} = ⋂ (m) (hm : s m ≤ s k), {ω | τ ω < s m} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun h m _ ↦ h m, fun h m ↦ ?_⟩
    rcases le_total (s m) (s k) with hmk | hkm
    · exact h m hmk
    · exact (h k le_rfl).trans_le (mod_cast hkm)
  rw [h_eq_k]
  exact MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun hm ↦ f.mono hm _ (hτ1 (s m))

lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous [DenselyOrdered ι] [NoMaxOrder ι]
    {τ : Ω → WithTop ι} [f.IsRightContinuous] (hτ : ∀ i, MeasurableSet[f i] {ω | τ ω < i}) :
    IsStoppingTime f τ :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous' hτ
    <| fun _ hi ↦ absurd hi (NeBot.ne inferInstance)

end IsRightContinuous

end MeasurableSet

namespace IsStoppingTime

protected theorem max [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun ω => max (τ ω) (π ω) := by
  intro i
  simp_rw [max_le_iff, Set.setOf_and]
  exact (hτ i).inter (hπ i)

protected theorem max_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => max (τ ω) i :=
  hτ.max (isStoppingTime_const f i)

protected theorem min [LinearOrder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f fun ω => min (τ ω) (π ω) := by
  intro i
  simp_rw [min_le_iff, Set.setOf_or]
  exact (hτ i).union (hπ i)

protected theorem min_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => min (τ ω) i :=
  hτ.min (isStoppingTime_const f i)

protected lemma biInf [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
    {κ : Type*} {f : Filtration ι m} {τ : κ → Ω → WithTop ι} {s : Set κ} (hs : s.Countable)
    [f.IsRightContinuous] (hτ : ∀ n ∈ s, IsStoppingTime f (τ n)) :
    IsStoppingTime f (fun ω ↦ ⨅ n ∈ s, τ n ω) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous <|
    fun i ↦ MeasurableSet.of_compl ?_
  rw [(_ : {ω | ⨅ n ∈ s, τ n ω < i}ᶜ = ⋂ n ∈ s, {ω | i ≤ τ n ω})]
  · exact MeasurableSet.biInter hs <| fun n hn ↦ (hτ n hn).measurableSet_ge i
  · ext ω
    simp

protected lemma iInf [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
    {κ : Type*} [Countable κ] {f : Filtration ι m} {τ : κ → Ω → WithTop ι}
    [f.IsRightContinuous] (hτ : ∀ n, IsStoppingTime f (τ n)) :
    IsStoppingTime f (fun ω ↦ ⨅ n, τ n ω) := by
  convert IsStoppingTime.biInf (κ := κ) Set.countable_univ (fun n _ => hτ n) using 2
  simp

theorem add_const [AddGroup ι] [Preorder ι] [AddRightMono ι]
    [AddLeftMono ι] {f : Filtration ι m} {τ : Ω → WithTop ι} (hτ : IsStoppingTime f τ)
    {i : ι} (hi : 0 ≤ i) : IsStoppingTime f fun ω => τ ω + i := by
  intro j
  simp only
  have h_eq : {ω | τ ω + i ≤ j} = {ω | τ ω ≤ j - i} := by
    ext ω
    simp only [Set.mem_setOf_eq, coe_sub]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp_rw [← le_sub_iff_add_le]
  rw [h_eq]
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))

theorem add_const' [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
    [TopologicalSpace ι] [OrderTopology ι]
    {f : Filtration ι m} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) :
    IsStoppingTime f fun ω => τ ω + i := by
  intro j
  have h : {ω | τ ω + i ≤ j} = ⋃ k : {k | k + i ≤ j}, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    cases τ ω with
    | top => simp
    | coe a => simp; norm_cast
  exact h ▸ MeasurableSet.iUnion fun k => hτ.measurableSet_eq_le (le_of_add_le_left k.2)

theorem add [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
    [TopologicalSpace ι] [OrderTopology ι]
    {f : Filtration ι m} {τ π : Ω → WithTop ι}
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f (τ + π) := by
  intro j
  have h : {ω | (τ + π) ω ≤ j} = ⋃ k : Set.Iic j, {ω | π ω = k} ∩ {ω | τ ω + k ≤ j} := by
    ext ω
    simp only [Pi.add_apply, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    cases τ ω with
    | top => simp
    | coe a =>
      cases π ω with
      | top => simp
      | coe b => norm_cast; simpa using le_of_add_le_right
  exact h ▸ MeasurableSet.iUnion fun k => (hπ.measurableSet_eq_le k.2).inter (hτ.add_const' k.1 j)

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ π : Ω → WithTop ι}
