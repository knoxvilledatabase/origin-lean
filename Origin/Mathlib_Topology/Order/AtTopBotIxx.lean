/-
Extracted from Topology/Order/AtTopBotIxx.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `Filter.atTop` and `Filter.atBot` for intervals in a linear order topology

Let `X` be a linear order with order topology.
Let `a` be a point that is either the bottom element of `X` or is not isolated on the left,
see `Order.IsSuccPrelimit`.
Then the `Filter.atTop` filter on `Set.Iio a` and `𝓝[<] a` are related by the coercion map
via pushforward and pullback, see `map_coe_Iio_atTop` and `comap_coe_Iio_nhdsLT`.

We prove several versions of this statement for `Set.Iio`, `Set.Ioi`, and `Set.Ioo`,
as well as `Filter.atTop` and `Filter.atBot`.

The assumption on `a` is automatically satisfied for densely ordered types,
see `Order.IsSuccPrelimit.of_dense`.
-/

open Set Filter Order OrderDual

open scoped Topology

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
  {s : Set X} {a b : X}

theorem comap_coe_nhdsLT_eq_atTop_iff :
    comap ((↑) : s → X) (𝓝[<] b) = atTop ↔
      s ⊆ Iio b ∧ (s.Nonempty → ∀ a < b, (s ∩ Ioo a b).Nonempty) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp [eq_iff_true_of_subsingleton]
  have := hsne.to_subtype
  simp only [hsne, true_imp_iff]
  by_cases hsub : s ⊆ Iio b
  · simp only [hsub, true_and]
    constructor
    · intro h a ha
      have := preimage_mem_comap (m := ((↑) : s → X)) (Ioo_mem_nhdsLT ha)
      rw [h] at this
      rcases Filter.nonempty_of_mem this with ⟨⟨c, hcs⟩, hc⟩
      exact ⟨c, hcs, hc⟩
    · intro h
      refine (nhdsLT_basis_of_exists_lt (hsne.mono hsub)).comap _ |>.ext atTop_basis ?_ ?_
      · intro a hab
        rcases h a hab with ⟨c, hcs, hc⟩
        use ⟨c, hcs⟩
        simp_all [subset_def, hc.1.trans_le]
      · rintro ⟨a, has⟩ -
        use a, hsub has
        simp_all [subset_def, le_of_lt]
  · suffices ¬Tendsto (↑) (atTop : Filter s) (𝓝[<] b) by
      contrapose this
      simp_all [tendsto_iff_comap]
    intro h
    rcases not_subset_iff_exists_mem_notMem.mp hsub with ⟨a, has, ha⟩
    rcases h.eventually eventually_mem_nhdsWithin |>.and (eventually_ge_atTop ⟨a, has⟩) |>.exists
      with ⟨⟨c, hcs⟩, hcb, hac⟩
    apply lt_irrefl a
    calc
      a ≤ c := by simpa using hac
      _ < b := by simpa using hcb
      _ ≤ a := by simpa using ha

theorem comap_coe_nhdsGT_eq_atBot_iff :
    comap ((↑) : s → X) (𝓝[>] b) = atBot ↔
      s ⊆ Ioi b ∧ (s.Nonempty → ∀ a > b, (s ∩ Ioo b a).Nonempty) := by
  refine comap_coe_nhdsLT_eq_atTop_iff (s := OrderDual.ofDual ⁻¹' s) (b := OrderDual.toDual b)
    |>.trans ?_
  simp [← preimage_inter, ofDual.surjective]

theorem comap_coe_nhdsLT_of_Ioo_subset (hsb : s ⊆ Iio b) (hs : s.Nonempty → ∃ a < b, Ioo a b ⊆ s)
    (hb : IsSuccPrelimit b := by exact .of_dense _) :
    comap ((↑) : s → X) (𝓝[<] b) = atTop := by
  rw [comap_coe_nhdsLT_eq_atTop_iff]
  refine ⟨hsb, fun hsne a ha ↦ ?_⟩
  rcases hs hsne with ⟨c, hcb, hcs⟩
  rcases hb.lt_iff_exists_lt.mp (max_lt ha hcb) with ⟨x, hxb, hacx⟩
  rw [max_lt_iff] at hacx
  exact ⟨x, hcs ⟨hacx.2, hxb⟩, hacx.1, hxb⟩

theorem comap_coe_nhdsGT_of_Ioo_subset (hsa : s ⊆ Ioi a) (hs : s.Nonempty → ∃ b > a, Ioo a b ⊆ s)
    (ha : IsPredPrelimit a := by exact .of_dense _) :
    comap ((↑) : s → X) (𝓝[>] a) = atBot := by
  refine comap_coe_nhdsLT_of_Ioo_subset (show ofDual ⁻¹' s ⊆ Iio (toDual a) from hsa) ?_ ha.dual
  simpa only [OrderDual.exists, Ioo_toDual]

theorem map_coe_atTop_of_Ioo_subset (hsb : s ⊆ Iio b) (hs : ∀ a' < b, ∃ a < b, Ioo a b ⊆ s)
    (hb : IsSuccPrelimit b := by exact .of_dense _) :
    map ((↑) : s → X) atTop = 𝓝[<] b := by
  rcases eq_empty_or_nonempty (Iio b) with (hb' | ⟨a, ha⟩)
  · have : IsEmpty s := ⟨fun x => hb'.subset (hsb x.2)⟩
    rw [filter_eq_bot_of_isEmpty atTop, Filter.map_bot, hb', nhdsWithin_empty]
  · rw [← comap_coe_nhdsLT_of_Ioo_subset hsb (fun _ => hs a ha) hb, map_comap_of_mem]
    rw [Subtype.range_val]
    exact (mem_nhdsLT_iff_exists_Ioo_subset' ha).2 (hs a ha)

theorem map_coe_atBot_of_Ioo_subset (hsa : s ⊆ Ioi a) (hs : ∀ b' > a, ∃ b > a, Ioo a b ⊆ s)
    (ha : IsPredPrelimit a := by exact .of_dense _) :
    map ((↑) : s → X) atBot = 𝓝[>] a := by
  refine map_coe_atTop_of_Ioo_subset (s := ofDual ⁻¹' s) (b := toDual a) hsa ?_ ha.dual
  intro b' hb'
  simpa [OrderDual.exists] using hs (ofDual b') hb'
