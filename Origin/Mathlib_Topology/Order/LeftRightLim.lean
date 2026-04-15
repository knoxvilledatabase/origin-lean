/-
Extracted from Topology/Order/LeftRightLim.lean
Genuine: 31 of 32 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Left and right limits

We define the (strict) left and right limits of a function.

* `leftLim f x` is the strict left limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its left).
* `rightLim f x` is the strict right limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its right).

We develop a comprehensive API for monotone functions. Notably,

* `Monotone.continuousAt_iff_leftLim_eq_rightLim` states that a monotone function is continuous
  at a point if and only if its left and right limits coincide.
* `Monotone.countable_not_continuousAt` asserts that a monotone function taking values in a
  second-countable space has at most countably many discontinuity points.

We also port the API to antitone functions.

## TODO

Prove corresponding stronger results for `StrictMono` and `StrictAnti` functions.
-/

open Set Filter

open Topology

variable {α β : Type*} [LinearOrder α] [TopologicalSpace β]

noncomputable def Function.leftLim (f : α → β) (a : α) : β := by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[<] a = ⊥ ∨ ¬∃ y, Tendsto f (𝓝[<] a) (𝓝 y) then f a else limUnder (𝓝[<] a) f

noncomputable def Function.rightLim (f : α → β) (a : α) : β :=
  @Function.leftLim αᵒᵈ β _ _ f a

open Function

set_option backward.isDefEq.respectTransparency false in

theorem leftLim_eq_of_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology α] [T2Space β]
    {f : α → β} {a : α} {y : β} (h : 𝓝[<] a ≠ ⊥) (h' : Tendsto f (𝓝[<] a) (𝓝 y)) :
    leftLim f a = y := by
  have h'' : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y) := ⟨y, h'⟩
  rw [h'α.topology_eq_generate_intervals] at h h' h''
  simp only [leftLim, h, h'', not_true, or_self_iff, if_false]
  haveI := neBot_iff.2 h
  exact lim_eq h'

theorem rightLim_eq_of_tendsto [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {a : α} {y : β} (h : 𝓝[>] a ≠ ⊥) (h' : Tendsto f (𝓝[>] a) (𝓝 y)) :
    Function.rightLim f a = y :=
  leftLim_eq_of_tendsto (α := αᵒᵈ) h h'

set_option backward.isDefEq.respectTransparency false in

theorem leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : 𝓝[<] a = ⊥) : leftLim f a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]

theorem rightLim_eq_of_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α → β) {a : α}
    (h : 𝓝[>] a = ⊥) : rightLim f a = f a :=
  leftLim_eq_of_eq_bot (α := αᵒᵈ) f h

set_option backward.isDefEq.respectTransparency false in

theorem leftLim_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : ¬ ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)) : leftLim f a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]

theorem rightLim_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : ¬ ∃ y, Tendsto f (𝓝[>] a) (𝓝 y)) : rightLim f a = f a :=
  leftLim_eq_of_not_tendsto (α := αᵒᵈ) f h

theorem leftLim_eq_of_isBot {f : α → β} {a : α} (ha : IsBot a) :
    leftLim f a = f a := by
  let A : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  apply leftLim_eq_of_eq_bot
  have : Iio a = ∅ := by simp; grind [IsBot, IsMin]
  simp [this]

theorem rightLim_eq_of_isTop {f : α → β} {a : α} (ha : IsTop a) :
    rightLim f a = f a :=
  leftLim_eq_of_isBot (α := αᵒᵈ) ha

theorem ContinuousWithinAt.leftLim_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {a : α} (hf : ContinuousWithinAt f (Iic a) a) : leftLim f a = f a := by
  rcases eq_or_ne (𝓝[<] a) ⊥ with h' | h'
  · simp [leftLim_eq_of_eq_bot f h']
  apply leftLim_eq_of_tendsto h'
  exact hf.tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)

theorem ContinuousWithinAt.rightLim_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {a : α} (hf : ContinuousWithinAt f (Ici a) a) : rightLim f a = f a :=
  ContinuousWithinAt.leftLim_eq (α := αᵒᵈ) hf

set_option backward.isDefEq.respectTransparency false in

theorem tendsto_leftLim_of_tendsto [TopologicalSpace α] [h'α : OrderTopology α]
    {f : α → β} {a : α} (h : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)) :
    Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a)) := by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [h']
  rw [h'α.topology_eq_generate_intervals] at h h' ⊢
  simp only [leftLim, neBot_iff.1 h', h, not_true_eq_false, or_self, ↓reduceIte]
  exact tendsto_nhds_limUnder h

theorem tendsto_rightLim_of_tendsto [TopologicalSpace α] [OrderTopology α]
    {f : α → β} {a : α} (h : ∃ y, Tendsto f (𝓝[>] a) (𝓝 y)) :
    Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a)) :=
  tendsto_leftLim_of_tendsto (α := αᵒᵈ) h

theorem mapClusterPt_leftLim [TopologicalSpace α] [OrderTopology α]
    (f : α → β) (a : α) : MapClusterPt (f.leftLim a) (𝓝[≤] a) f := by
  have A : (𝓝 (f a) ⊓ map f (𝓝[≤] a)).NeBot := by
    refine inf_neBot_iff.mpr (fun s hs s' hs' ↦ ?_)
    refine ⟨f a, mem_of_mem_nhds hs, ?_⟩
    simp only [mem_map] at hs'
    apply mem_of_mem_nhdsWithin self_mem_Iic hs'
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp only [MapClusterPt, ClusterPt, h', leftLim_eq_of_eq_bot, A]
  by_cases! H : ¬ ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)
  · simp [MapClusterPt, ClusterPt, H, leftLim_eq_of_not_tendsto, A]
  have : MapClusterPt (f.leftLim a) (𝓝[<] a) f := (tendsto_leftLim_of_tendsto H).mapClusterPt
  exact MapClusterPt.mono this (nhdsWithin_mono _ Iio_subset_Iic_self)

theorem mapClusterPt_rightLim [TopologicalSpace α] [OrderTopology α]
    (f : α → β) (a : α) : MapClusterPt (f.rightLim a) (𝓝[≥] a) f :=
  mapClusterPt_leftLim (α := αᵒᵈ) _ _

theorem continuousWithinAt_leftLim_Iic [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) :
    ContinuousWithinAt f.leftLim (Iic a) a := by
  have : 𝓝[≤] a = 𝓝[<] a ⊔ pure a := by
    rw [← Iio_union_Icc_eq_Iic le_rfl, nhdsWithin_union]
    simp
  rw [ContinuousWithinAt, this, tendsto_sup]
  simp only [tendsto_pure_nhds, and_true]
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [h']
  obtain ⟨b, hb⟩ : (Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  obtain ⟨u, au, hu⟩ : ∃ u, u < a ∧ Ioo u a ⊆ {x | f x ∈ s} := by
    have := (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.1 h s ⟨s_mem, s_closed⟩
    simpa using (mem_nhdsLT_iff_exists_Ioo_subset' hb).1 this
  filter_upwards [Ioo_mem_nhdsLT au] with c hc
  rcases eq_or_neBot (𝓝[<] c) with h'c | h'c
  · simpa [h'c, leftLim_eq_of_eq_bot] using hu hc
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[<] c) (𝓝 y)
  · simpa [leftLim_eq_of_not_tendsto _ h''c] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_leftLim_of_tendsto h''c)
  filter_upwards [Ioo_mem_nhdsLT_of_mem ⟨hc.1, hc.2.le⟩] with d hd using hu hd

theorem leftLim_leftLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) :
    f.leftLim.leftLim a = f.leftLim a :=
  (continuousWithinAt_leftLim_Iic h).leftLim_eq

theorem continuousWithinAt_rightLim_Ici [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) :
    ContinuousWithinAt f.rightLim (Ici a) a :=
  continuousWithinAt_leftLim_Iic (α := αᵒᵈ) h

theorem rightLim_rightLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) :
    f.rightLim.rightLim a = f.rightLim a :=
  leftLim_leftLim (α := αᵒᵈ) h

theorem leftLim_rightLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) [h' : (𝓝[<] a).NeBot] :
    f.rightLim.leftLim a = f.leftLim a := by
  obtain ⟨b, hb⟩ : (Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  apply leftLim_eq_of_tendsto (neBot_iff.mp h')
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, au, hu⟩ : ∃ u, u < a ∧ Ioo u a ⊆ {x | f x ∈ s} := by
    have := (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.1 h s ⟨s_mem, s_closed⟩
    simpa using (mem_nhdsLT_iff_exists_Ioo_subset' hb).1 this
  filter_upwards [Ioo_mem_nhdsLT au] with c hc
  rcases eq_or_neBot (𝓝[>] c) with h'c | h'c
  · simpa [h'c, rightLim_eq_of_eq_bot] using hu hc
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[>] c) (𝓝 y)
  · simpa [rightLim_eq_of_not_tendsto _ h''c] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_rightLim_of_tendsto h''c)
  filter_upwards [Ioo_mem_nhdsGT_of_mem ⟨hc.1.le, hc.2⟩] with d hd using hu hd

theorem tendsto_atTop_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] [T3Space β] [NoTopOrder α] {f g : α → β} {b : β}
    (h : Tendsto f atTop (𝓝 b)) (h' : ∀ᶠ x in atTop, MapClusterPt (g x) (𝓝 x) f) :
    Tendsto g atTop (𝓝 b) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [filter_eq_bot_of_isEmpty atTop]
  apply (closed_nhds_basis b).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, hu⟩ : ∃ a, ∀ (b : α), a ≤ b → MapClusterPt (g b) (𝓝 b) f ∧ f b ∈ s := by
    simpa [eventually_atTop] using h'.and (h s_mem)
  filter_upwards [Ioi_mem_atTop u] with a (ha : u < a)
  apply s_closed.mem_of_mapClusterPt (hu a ha.le).1
  filter_upwards [Ici_mem_nhds ha] with y hy using (hu y hy).2

theorem tendsto_atBot_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] [T3Space β] [NoBotOrder α] {f g : α → β} {b : β}
    (h : Tendsto f atBot (𝓝 b)) (h' : ∀ᶠ x in atBot, MapClusterPt (g x) (𝓝 x) f) :
    Tendsto g atBot (𝓝 b) :=
  tendsto_atTop_of_mapClusterPt (α := αᵒᵈ) h h'

theorem tendsto_leftLim_atTop_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [NoTopOrder α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atTop (𝓝 b)) :
    Tendsto f.leftLim atTop (𝓝 b) := by
  apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
  exact MapClusterPt.mono (mapClusterPt_leftLim _ _) nhdsWithin_le_nhds

theorem tendsto_rightLim_atTop_of_tendsto [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atTop (𝓝 b)) :
    Tendsto f.rightLim atTop (𝓝 b) := by
  cases topOrderOrNoTopOrder α
  · simp only [OrderTop.atTop_eq α] at h ⊢
    have : f.rightLim ⊤ = f ⊤ := rightLim_eq_of_isTop isTop_top
    rw [tendsto_nhds_unique h (tendsto_pure_nhds f ⊤), ← this]
    apply tendsto_pure_nhds
  · apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
    exact MapClusterPt.mono (mapClusterPt_rightLim _ _) nhdsWithin_le_nhds

theorem tendsto_rightLim_atBot_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [NoBotOrder α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atBot (𝓝 b)) :
    Tendsto f.rightLim atBot (𝓝 b) :=
  tendsto_leftLim_atTop_of_tendsto (α := αᵒᵈ) h

theorem tendsto_leftLim_atBot_of_tendsto [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atBot (𝓝 b)) :
    Tendsto f.leftLim atBot (𝓝 b) :=
  tendsto_rightLim_atTop_of_tendsto (α := αᵒᵈ) h

end

open Function

namespace Monotone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Monotone f) {x y : α}

include hf

theorem leftLim_eq_sSup [TopologicalSpace α] [OrderTopology α] (h : 𝓝[<] x ≠ ⊥) :
    leftLim f x = sSup (f '' Iio x) :=
  leftLim_eq_of_tendsto h (hf.tendsto_nhdsLT x)

theorem rightLim_eq_sInf [TopologicalSpace α] [OrderTopology α] (h : 𝓝[>] x ≠ ⊥) :
    rightLim f x = sInf (f '' Ioi x) :=
  rightLim_eq_of_tendsto h (hf.tendsto_nhdsGT x)

theorem leftLim_le (h : x ≤ y) : leftLim f x ≤ f y := by
  letI : TopologicalSpace α := Preorder.topology α
  haveI : OrderTopology α := ⟨rfl⟩
  rcases eq_or_ne (𝓝[<] x) ⊥ with (h' | h')
  · simpa [leftLim, h'] using hf h
  haveI A : NeBot (𝓝[<] x) := neBot_iff.2 h'
  rw [leftLim_eq_sSup hf h']
  refine csSup_le ?_ ?_
  · simp only [image_nonempty]
    exact (forall_mem_nonempty_iff_neBot.2 A) _ self_mem_nhdsWithin
  · simp only [mem_image, mem_Iio, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro z hz
    exact hf (hz.le.trans h)

theorem le_leftLim (h : x < y) : f x ≤ leftLim f y := by
  letI : TopologicalSpace α := Preorder.topology α
  haveI : OrderTopology α := ⟨rfl⟩
  rcases eq_or_ne (𝓝[<] y) ⊥ with (h' | h')
  · rw [leftLim_eq_of_eq_bot _ h']
    exact hf h.le
  rw [leftLim_eq_sSup hf h']
  refine le_csSup ⟨f y, ?_⟩ (mem_image_of_mem _ h)
  simp only [upperBounds, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_setOf_eq]
  intro z hz
  exact hf hz.le
