/-
Extracted from Topology/Order/LeftRightNhds.lean
Genuine: 30 of 33 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Neighborhoods to the left and to the right on an `OrderTopology`

We've seen some properties of left and right neighborhood of a point in an `OrderClosedTopology`.
In an `OrderTopology`, such neighborhoods can be characterized as the sets containing suitable
intervals to the right or to the left of `a`. We give now these characterizations. -/

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β γ : Type*}

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α]

section OrderTopology

variable [OrderTopology α]

open List in

theorem TFAE_mem_nhdsGT {a b : α} (hab : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[>] a,
      s ∈ 𝓝[Ioc a b] a,
      s ∈ 𝓝[Ioo a b] a,
      ∃ u ∈ Ioc a b, Ioo a u ⊆ s,
      ∃ u ∈ Ioi a, Ioo a u ⊆ s] := by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hab]
  tfae_have 4 → 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 → 1
  | ⟨u, hau, hu⟩ => mem_of_superset (Ioo_mem_nhdsGT hau) hu
  tfae_have 1 → 4
  | h => by
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 h with ⟨v, va, hv⟩
    rcases exists_Ico_subset_of_mem_nhds' va hab with ⟨u, au, hu⟩
    exact ⟨u, au, fun x hx => hv ⟨hu ⟨le_of_lt hx.1, hx.2⟩, hx.1⟩⟩
  tfae_finish

theorem mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioc a u', Ioo a u ⊆ s :=
  (TFAE_mem_nhdsGT hu' s).out 0 3

theorem mem_nhdsGT_iff_exists_Ioo_subset' {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioo a u ⊆ s :=
  (TFAE_mem_nhdsGT hu' s).out 0 4

lemma nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a < ·) (Ioo a) :=
  nhdsGT_basis_of_exists_gt <| exists_gt a

theorem nhdsGT_eq_bot_iff {a : α} : 𝓝[>] a = ⊥ ↔ IsTop a ∨ ∃ b, a ⋖ b := by
  by_cases ha : IsTop a
  · simp [ha, ha.isMax.Ioi_eq]
  · simp only [ha, false_or]
    rw [isTop_iff_isMax, not_isMax_iff] at ha
    simp only [(nhdsGT_basis_of_exists_gt ha).eq_bot_iff, covBy_iff_Ioo_eq]

theorem mem_nhdsGT_iff_exists_Ioo_subset [NoMaxOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioo a u ⊆ s :=
  let ⟨_u', hu'⟩ := exists_gt a
  mem_nhdsGT_iff_exists_Ioo_subset' hu'

theorem countable_setOf_isolated_right [SecondCountableTopology α] :
    { x : α | 𝓝[>] x = ⊥ }.Countable := by
  simp only [nhdsGT_eq_bot_iff, setOf_or]
  exact (subsingleton_isTop α).countable.union countable_setOf_covBy_right

theorem countable_setOf_isolated_left [SecondCountableTopology α] :
    { x : α | 𝓝[<] x = ⊥ }.Countable :=
  countable_setOf_isolated_right (α := αᵒᵈ)

theorem countable_setOf_isolated_right_within [SecondCountableTopology α] {s : Set α} :
    { x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥ }.Countable := by
  /- This does not follow from `countable_setOf_isolated_right`, which gives the result when `s`
  is the whole space, as one cannot use it inside the subspace since it doesn't have the order
  topology. Instead, we follow the main steps of its proof. -/
  let t := { x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥ ∧ ¬ IsTop x}
  suffices H : t.Countable by
    have : { x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥ } ⊆ t ∪ {x | IsTop x} := by
      intro x hx
      by_cases h'x : IsTop x
      · simp [h'x]
      · simpa [-sep_and, t, h'x]
    apply Countable.mono this
    simp [H, (subsingleton_isTop α).countable]
  have (x) (hx : x ∈ t) : ∃ y > x, s ∩ Ioo x y = ∅ := by
    simp only [← empty_mem_iff_bot, mem_nhdsWithin_iff_exists_mem_nhds_inter,
      subset_empty_iff, IsTop, not_forall, not_le, mem_setOf_eq, t] at hx
    rcases hx.2.1 with ⟨u, hu, h'u⟩
    obtain ⟨y, hxy, hy⟩ : ∃ y, x < y ∧ Ico x y ⊆ u := exists_Ico_subset_of_mem_nhds hu hx.2.2
    refine ⟨y, hxy, ?_⟩
    contrapose! h'u
    apply h'u.mono
    intro z hz
    exact ⟨hy ⟨hz.2.1.le, hz.2.2⟩, hz.1, hz.2.1⟩
  choose! y hy h'y using this
  apply Set.PairwiseDisjoint.countable_of_Ioo (y := y) _ hy
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun]
  intro a ha b hb hab
  wlog! H : a < b generalizing a b with h
  · have : b < a := lt_of_le_of_ne H hab.symm
    exact (h hb ha hab.symm this).symm
  have : y a ≤ b := by
    by_contra!
    have : b ∈ s ∩ Ioo a (y a) := by simp [hb.1, H, this]
    simp [h'y a ha] at this
  rw [disjoint_iff_forall_ne]
  exact fun u hu v hv ↦ ((hu.2.trans_le this).trans hv.1).ne

theorem countable_setOf_isolated_left_within [SecondCountableTopology α] {s : Set α} :
    { x ∈ s | 𝓝[s ∩ Iio x] x = ⊥ }.Countable :=
  countable_setOf_isolated_right_within (α := αᵒᵈ)

theorem mem_nhdsGT_iff_exists_Ioc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioc a u ⊆ s := by
  rw [mem_nhdsGT_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨u, au, as⟩
    rcases exists_between au with ⟨v, hv⟩
    exact ⟨v, hv.1, fun x hx => as ⟨hx.1, lt_of_le_of_lt hx.2 hv.2⟩⟩
  · rintro ⟨u, au, as⟩
    exact ⟨u, au, Subset.trans Ioo_subset_Ioc_self as⟩

open List in

theorem TFAE_mem_nhdsLT {a b : α} (h : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[<] b, -- 0 : `s` is a neighborhood of `b` within `(-∞, b)`
        s ∈ 𝓝[Ico a b] b, -- 1 : `s` is a neighborhood of `b` within `[a, b)`
        s ∈ 𝓝[Ioo a b] b, -- 2 : `s` is a neighborhood of `b` within `(a, b)`
        ∃ l ∈ Ico a b, Ioo l b ⊆ s, -- 3 : `s` includes `(l, b)` for some `l ∈ [a, b)`
        ∃ l ∈ Iio b, Ioo l b ⊆ s] := by -- 4 : `s` includes `(l, b)` for some `l < b`
  simpa using TFAE_mem_nhdsGT h.dual (ofDual ⁻¹' s)

theorem mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Ico l' a, Ioo l a ⊆ s :=
  (TFAE_mem_nhdsLT hl' s).out 0 3

theorem mem_nhdsLT_iff_exists_Ioo_subset' {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ioo l a ⊆ s :=
  (TFAE_mem_nhdsLT hl' s).out 0 4

theorem mem_nhdsLT_iff_exists_Ioo_subset [NoMinOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ioo l a ⊆ s :=
  let ⟨_, h⟩ := exists_lt a
  mem_nhdsLT_iff_exists_Ioo_subset' h

theorem mem_nhdsLT_iff_exists_Ico_subset [NoMinOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ico l a ⊆ s := by
  have : ofDual ⁻¹' s ∈ 𝓝[>] toDual a ↔ _ := mem_nhdsGT_iff_exists_Ioc_subset
  simpa using this

theorem nhdsLT_basis [NoMinOrder α] (a : α) : (𝓝[<] a).HasBasis (· < a) (Ioo · a) :=
  nhdsLT_basis_of_exists_lt <| exists_lt a

theorem nhdsLT_eq_bot_iff {a : α} : 𝓝[<] a = ⊥ ↔ IsBot a ∨ ∃ b, b ⋖ a := by
  convert (config := { preTransparency := .default }) nhdsGT_eq_bot_iff (a := OrderDual.toDual a)
    using 4
  exact ofDual_covBy_ofDual_iff

open List in

theorem TFAE_mem_nhdsGE {a b : α} (hab : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[≥] a,
      s ∈ 𝓝[Icc a b] a,
      s ∈ 𝓝[Ico a b] a,
      ∃ u ∈ Ioc a b, Ico a u ⊆ s,
      ∃ u ∈ Ioi a, Ico a u ⊆ s] := by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Icc_eq_nhdsGE hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ico_eq_nhdsGE hab]
  tfae_have 1 ↔ 5 := (nhdsGE_basis_of_exists_gt ⟨b, hab⟩).mem_iff
  tfae_have 4 → 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 → 4
  | ⟨u, hua, hus⟩ => ⟨min u b, ⟨lt_min hua hab, min_le_right _ _⟩,
      (Ico_subset_Ico_right <| min_le_left _ _).trans hus⟩
  tfae_finish

theorem mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioc a u', Ico a u ⊆ s :=
  (TFAE_mem_nhdsGE hu' s).out 0 3 (by simp) (by simp)

theorem mem_nhdsGE_iff_exists_Ico_subset' {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioi a, Ico a u ⊆ s :=
  (TFAE_mem_nhdsGE hu' s).out 0 4 (by simp) (by simp)

theorem mem_nhdsGE_iff_exists_Ico_subset [NoMaxOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioi a, Ico a u ⊆ s :=
  let ⟨_, hu'⟩ := exists_gt a
  mem_nhdsGE_iff_exists_Ico_subset' hu'

theorem nhdsGE_basis_Ico [NoMaxOrder α] (a : α) : (𝓝[≥] a).HasBasis (fun u => a < u) (Ico a) :=
  ⟨fun _ => mem_nhdsGE_iff_exists_Ico_subset⟩

theorem nhdsGE_basis_Icc [NoMaxOrder α] [DenselyOrdered α] {a : α} :
    (𝓝[≥] a).HasBasis (a < ·) (Icc a) :=
  (nhdsGE_basis _).to_hasBasis
    (fun _u hu ↦ (exists_between hu).imp fun _v hv ↦ hv.imp_right Icc_subset_Ico_right) fun u hu ↦
    ⟨u, hu, Ico_subset_Icc_self⟩

theorem mem_nhdsGE_iff_exists_Icc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s ∈ 𝓝[≥] a ↔ ∃ u, a < u ∧ Icc a u ⊆ s :=
  nhdsGE_basis_Icc.mem_iff

open List in

theorem TFAE_mem_nhdsLE {a b : α} (h : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[≤] b, -- 0 : `s` is a neighborhood of `b` within `(-∞, b]`
      s ∈ 𝓝[Icc a b] b, -- 1 : `s` is a neighborhood of `b` within `[a, b]`
      s ∈ 𝓝[Ioc a b] b, -- 2 : `s` is a neighborhood of `b` within `(a, b]`
      ∃ l ∈ Ico a b, Ioc l b ⊆ s, -- 3 : `s` includes `(l, b]` for some `l ∈ [a, b)`
      ∃ l ∈ Iio b, Ioc l b ⊆ s] := by -- 4 : `s` includes `(l, b]` for some `l < b`
  simpa using TFAE_mem_nhdsGE h.dual (ofDual ⁻¹' s)

theorem mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Ico l' a, Ioc l a ⊆ s :=
  (TFAE_mem_nhdsLE hl' s).out 0 3 (by simp) (by simp)

theorem mem_nhdsLE_iff_exists_Ioc_subset' {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Iio a, Ioc l a ⊆ s :=
  (TFAE_mem_nhdsLE hl' s).out 0 4 (by simp) (by simp)

theorem mem_nhdsLE_iff_exists_Ioc_subset [NoMinOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Iio a, Ioc l a ⊆ s :=
  let ⟨_, hl'⟩ := exists_lt a
  mem_nhdsLE_iff_exists_Ioc_subset' hl'

theorem nhdsLE_basis_Icc [NoMinOrder α] [DenselyOrdered α] {a : α} :
    (𝓝[≤] a).HasBasis (· < a) (Icc · a) :=
  ⟨fun _ ↦ mem_nhdsLE_iff_exists_Icc_subset⟩

end OrderTopology

end LinearOrder

section LinearOrderedCommGroup

variable [TopologicalSpace α] [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]
  [OrderTopology α]

variable {l : Filter β} {f g : β → α}
