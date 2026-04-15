/-
Extracted from Topology/Order/LiminfLimsup.lean
Genuine: 36 of 52 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core

/-!
# Lemmas about liminf and limsup in an order topology.

## Main declarations

* `BoundedLENhdsClass`: Typeclass stating that neighborhoods are eventually bounded above.
* `BoundedGENhdsClass`: Typeclass stating that neighborhoods are eventually bounded below.

## Implementation notes

The same lemmas are true in `ℝ`, `ℝ × ℝ`, `ι → ℝ`, `EuclideanSpace ι ℝ`. To avoid code
duplication, we provide an ad hoc axiomatisation of the properties we need.
-/

open Filter TopologicalSpace

open scoped Topology

universe u v

variable {ι α β R S : Type*} {π : ι → Type*}

class BoundedLENhdsClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·)

class BoundedGENhdsClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·)

section Preorder

variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]

section BoundedLENhdsClass

variable [BoundedLENhdsClass α] [BoundedLENhdsClass β] {f : Filter ι} {u : ι → α} {a : α}

theorem isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·) :=
  BoundedLENhdsClass.isBounded_le_nhds _

theorem Filter.Tendsto.isBoundedUnder_le (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≤ ·) u :=
  (isBounded_le_nhds a).mono h

theorem isCobounded_ge_nhds (a : α) : (𝓝 a).IsCobounded (· ≥ ·) :=
  (isBounded_le_nhds a).isCobounded_flip

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): Prod.instBoundedLENhdsClass

-- INSTANCE (free from Core): Pi.instBoundedLENhdsClass

end BoundedLENhdsClass

section BoundedGENhdsClass

variable [BoundedGENhdsClass α] [BoundedGENhdsClass β] {f : Filter ι} {u : ι → α} {a : α}

theorem isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·) :=
  BoundedGENhdsClass.isBounded_ge_nhds _

theorem Filter.Tendsto.isBoundedUnder_ge (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≥ ·) u :=
  (isBounded_ge_nhds a).mono h

theorem isCobounded_le_nhds (a : α) : (𝓝 a).IsCobounded (· ≤ ·) :=
  (isBounded_ge_nhds a).isCobounded_flip

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): Prod.instBoundedGENhdsClass

-- INSTANCE (free from Core): Pi.instBoundedGENhdsClass

end BoundedGENhdsClass

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end Preorder

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

section LiminfLimsup

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]

theorem le_nhds_of_limsSup_eq_limsInf {f : Filter α} {a : α} (hl : f.IsBounded (· ≤ ·))
    (hg : f.IsBounded (· ≥ ·)) (hs : f.limsSup = a) (hi : f.limsInf = a) : f ≤ 𝓝 a :=
  tendsto_order.2 ⟨fun _ hb ↦ gt_mem_sets_of_limsInf_gt hg <| hi.symm ▸ hb,
    fun _ hb ↦ lt_mem_sets_of_limsSup_lt hl <| hs.symm ▸ hb⟩

theorem limsSup_nhds (a : α) : limsSup (𝓝 a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt (isBounded_le_nhds a)
    (fun a' (h : { n : α | n ≤ a' } ∈ 𝓝 a) ↦ show a ≤ a' from @mem_of_mem_nhds _ _ a _ h)
    fun b (hba : a < b) ↦
    show ∃ c, { n : α | n ≤ c } ∈ 𝓝 a ∧ c < b from
      match dense_or_discrete a b with
      | Or.inl ⟨c, hac, hcb⟩ => ⟨c, ge_mem_nhds hac, hcb⟩
      | Or.inr ⟨_, h⟩ => ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩

theorem limsInf_nhds (a : α) : limsInf (𝓝 a) = a :=
  limsSup_nhds (α := αᵒᵈ) a

theorem limsInf_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f ≤ 𝓝 a) : f.limsInf = a :=
  have hb_ge : IsBounded (· ≥ ·) f := (isBounded_ge_nhds a).mono h
  have hb_le : IsBounded (· ≤ ·) f := (isBounded_le_nhds a).mono h
  le_antisymm
    (calc
      f.limsInf ≤ f.limsSup := limsInf_le_limsSup hb_le hb_ge
      _ ≤ (𝓝 a).limsSup := limsSup_le_limsSup_of_le h hb_ge.isCobounded_flip (isBounded_le_nhds a)
      _ = a := limsSup_nhds a)
    (calc
      a = (𝓝 a).limsInf := (limsInf_nhds a).symm
      _ ≤ f.limsInf := limsInf_le_limsInf_of_le h (isBounded_ge_nhds a) hb_le.isCobounded_flip)

set_option backward.isDefEq.respectTransparency false in

theorem limsSup_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f ≤ 𝓝 a) : f.limsSup = a :=
  limsInf_eq_of_le_nhds (α := αᵒᵈ) h

theorem Filter.Tendsto.limsup_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : limsup u f = a :=
  limsSup_eq_of_le_nhds h

theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : liminf u f = a :=
  limsInf_eq_of_le_nhds h

theorem ClusterPt.limsSup {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≤ ·) := by isBoundedDefault) : ClusterPt f.limsSup f := by
  by_cases! hn : Nontrivial α
  · by_cases! htop : ∀ x, x ≤ f.limsSup
    · let : OrderTop α := { top := f.limsSup, le_top := htop }
      exact nhds_top_basis.clusterPt_iff_frequently |>.mpr fun a => frequently_lt_of_lt_limsSup hc
    · by_cases! hbot : ∀ x, f.limsSup ≤ x
      · let : OrderBot α := { bot := f.limsSup, bot_le := hbot }
        refine nhds_bot_basis.clusterPt_iff_frequently |>.mpr fun a h => ?_
        exact lt_mem_sets_of_limsSup_lt hb h |>.frequently
      · refine (nhds_basis_Ioo' hbot htop).clusterPt_iff_frequently |>.mpr fun a ⟨hl, hg⟩ => ?_
        exact frequently_lt_of_lt_limsSup hc hl |>.and_eventually <| lt_mem_sets_of_limsSup_lt hb hg
  · simp_all [ClusterPt, Filter.eq_top_of_neBot]

set_option backward.isDefEq.respectTransparency false in

theorem ClusterPt.limsInf {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≥ ·) := by isBoundedDefault) : ClusterPt f.limsInf f :=
  ClusterPt.limsSup (α := αᵒᵈ) hc hb

theorem ClusterPt.le_limsSup {f : Filter α} {x : α} (hx : ClusterPt x f)
    (hb : f.IsBounded (· ≤ ·) := by isBoundedDefault) :
    x ≤ f.limsSup := by
  simp only [ClusterPt] at hx
  have : (𝓝 x ⊓ f).limsSup = x := limsSup_eq_of_le_nhds inf_le_left
  refine this ▸ limsSup_le_limsSup_of_le inf_le_right ?_ hb
  exact (IsBounded.mono inf_le_left (isBounded_ge_nhds x)).isCobounded_le

theorem ClusterPt.limsInf_le {f : Filter α} {x : α} (hx : ClusterPt x f)
    (hb : f.IsBounded (· ≥ ·) := by isBoundedDefault) :
    f.limsInf ≤ x :=
  hx.le_limsSup (α := αᵒᵈ)

theorem isGreatest_clusterPt_limsSup {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≤ ·) := by isBoundedDefault) :
    IsGreatest {x | ClusterPt x f} f.limsSup :=
  ⟨ClusterPt.limsSup, fun a ha => ha.le_limsSup⟩

set_option backward.isDefEq.respectTransparency false in

theorem isLeast_clusterPt_limsInf {f : Filter α} [NeBot f]
    (hc : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≥ ·) := by isBoundedDefault) :
    IsLeast {x | ClusterPt x f} f.limsInf :=
  isGreatest_clusterPt_limsSup (α := αᵒᵈ)

theorem MapClusterPt.limsup {u : β → α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· ≤ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    MapClusterPt (f.limsup u) f u :=
  ClusterPt.limsSup

theorem MapClusterPt.liminf {u : β → α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· ≥ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    MapClusterPt (liminf u f) f u :=
  ClusterPt.limsInf

theorem MapClusterPt.le_limsup {u : β → α} {f : Filter β}
    {x : α} (hx : MapClusterPt x f u) (hb : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    x ≤ f.limsup u :=
  hx.le_limsSup

theorem MapClusterPt.liminf_le {u : β → α} {f : Filter β}
    {x : α} (hx : MapClusterPt x f u) (hb : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    f.liminf u ≤ x :=
  hx.limsInf_le

theorem isGreatest_mapClusterPt_limsup {u : β → α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· ≤ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    IsGreatest {x | MapClusterPt x f u} (limsup u f) :=
  isGreatest_clusterPt_limsSup

theorem isLeast_mapClusterPt_liminf {u : β → α} {f : Filter β} [NeBot f]
    (hc : IsCoboundedUnder (· ≥ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    IsLeast {x | MapClusterPt x f u} (liminf u f) :=
  isLeast_clusterPt_limsInf

theorem tendsto_of_liminf_eq_limsup {f : Filter β} {u : β → α} {a : α} (hinf : liminf u f = a)
    (hsup : limsup u f = a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a) :=
  le_nhds_of_limsSup_eq_limsInf h h' hsup hinf

theorem tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminf u f)
    (hsup : limsup u f ≤ a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a) := by
  rcases f.eq_or_neBot with rfl | _
  · exact tendsto_bot
  · exact tendsto_of_liminf_eq_limsup (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
      (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'

theorem tendsto_of_no_upcrossings [DenselyOrdered α] {f : Filter β} {u : β → α} {s : Set α}
    (hs : Dense s) (H : ∀ a ∈ s, ∀ b ∈ s, a < b → ¬((∃ᶠ n in f, u n < a) ∧ ∃ᶠ n in f, b < u n))
    (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    ∃ c : α, Tendsto u f (𝓝 c) := by
  rcases f.eq_or_neBot with rfl | hbot
  · exact ⟨sInf ∅, tendsto_bot⟩
  refine ⟨limsup u f, ?_⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'
  by_contra! hlt
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : ∃ a, (f.liminf u < a ∧ a < f.limsup u) ∧ a ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo (f.liminf u) (f.limsup u)) isOpen_Ioo
      (Set.nonempty_Ioo.2 hlt)
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : ∃ b, (a < b ∧ b < f.limsup u) ∧ b ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo a (f.limsup u)) isOpen_Ioo (Set.nonempty_Ioo.2 au)
  have A : ∃ᶠ n in f, u n < a := frequently_lt_of_liminf_lt (IsBounded.isCobounded_ge h) la
  have B : ∃ᶠ n in f, b < u n := frequently_lt_of_lt_limsup (IsBounded.isCobounded_le h') bu
  exact H a as b bs ab ⟨A, B⟩

variable [FirstCountableTopology α] {f : Filter α}

theorem exists_seq_tendsto_limsSup [NeBot f] [IsCountablyGenerated f]
    (hc : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≤ ·) := by isBoundedDefault) :
    ∃ x : ℕ → α, Tendsto x atTop (𝓝 f.limsSup) ∧ Tendsto x atTop f :=
  (ClusterPt.limsSup).exists_seq_tendsto

theorem exists_seq_tendsto_limsInf [NeBot f] [IsCountablyGenerated f]
    (hc : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (hb : f.IsBounded (· ≥ ·) := by isBoundedDefault) :
    ∃ x : ℕ → α, Tendsto x atTop (𝓝 f.limsInf) ∧ Tendsto x atTop f :=
  (ClusterPt.limsInf).exists_seq_tendsto

variable {f : Filter β}

theorem exists_seq_tendsto_limsup [NeBot f] [IsCountablyGenerated f] {u : β → α}
    (hc : IsCoboundedUnder (· ≤ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    ∃ x : ℕ → β, Tendsto (u ∘ x) atTop (𝓝 (limsup u f)) ∧ Tendsto x atTop f :=
  (MapClusterPt.limsup).exists_seq_tendsto

theorem exists_seq_tendsto_liminf [NeBot f] {u : β → α} [IsCountablyGenerated f]
    (hc : IsCoboundedUnder (· ≥ ·) f u := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    ∃ x : ℕ → β, Tendsto (u ∘ x) atTop (𝓝 (liminf u f)) ∧ Tendsto x atTop f :=
  (MapClusterPt.liminf).exists_seq_tendsto

variable [CountableInterFilter f] {u : β → α}

theorem eventually_le_limsup (hf : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    ∀ᶠ b in f, u b ≤ f.limsup u := by
  obtain ha | ha := isTop_or_exists_gt (f.limsup u)
  · exact Eventually.of_forall fun _ => ha _
  by_cases H : IsGLB (Set.Ioi (f.limsup u)) (f.limsup u)
  · obtain ⟨u, -, -, hua, hu⟩ := H.exists_seq_antitone_tendsto ha
    have := fun n => eventually_lt_of_limsup_lt (hu n) hf
    exact
      (eventually_countable_forall.2 this).mono fun b hb =>
        ge_of_tendsto hua <| Eventually.of_forall fun n => (hb _).le
  · obtain ⟨x, hx, xa⟩ : ∃ x, (∀ ⦃b⦄, f.limsup u < b → x ≤ b) ∧ f.limsup u < x := by
      simp only [IsGLB, IsGreatest, lowerBounds, upperBounds, Set.mem_Ioi, Set.mem_setOf_eq,
        not_and, not_forall, not_le, exists_prop] at H
      exact H fun x => le_of_lt
    filter_upwards [eventually_lt_of_limsup_lt xa hf] with y hy
    contrapose! hy
    exact hx hy

theorem eventually_liminf_le (hf : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    ∀ᶠ b in f, f.liminf u ≤ u b :=
  eventually_le_limsup (α := αᵒᵈ) hf

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [TopologicalSpace α] [FirstCountableTopology α] [OrderTopology α]
  {f : Filter β} [CountableInterFilter f] {u : β → α}
