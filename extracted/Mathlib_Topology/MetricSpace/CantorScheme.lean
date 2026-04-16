/-
Extracted from Topology/MetricSpace/CantorScheme.lean
Genuine: 12 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Topology.MetricSpace.PiNat

noncomputable section

/-!
# (Topological) Schemes and their induced maps

In topology, and especially descriptive set theory, one often constructs functions `(ℕ → β) → α`,
where α is some topological space and β is a discrete space, as an appropriate limit of some map
`List β → Set α`. We call the latter type of map a "`β`-scheme on `α`".

This file develops the basic, abstract theory of these schemes and the functions they induce.

## Main Definitions

* `CantorScheme.inducedMap A` : The aforementioned "limit" of a scheme `A : List β → Set α`.
  This is a partial function from `ℕ → β` to `a`,
  implemented here as an object of type `Σ s : Set (ℕ → β), s → α`.
  That is, `(inducedMap A).1` is the domain and `(inducedMap A).2` is the function.

## Implementation Notes

We consider end-appending to be the fundamental way to build lists (say on `β`) inductively,
as this interacts better with the topology on `ℕ → β`.
As a result, functions like `List.get?` or `Stream'.take` do not have their intended meaning
in this file. See instead `PiNat.res`.

## References

* [kechris1995] (Chapters 6-7)

## Tags

scheme, cantor scheme, lusin scheme, approximation.

-/

namespace CantorScheme

open List Function Filter Set PiNat Topology

variable {β α : Type*} (A : List β → Set α)

noncomputable def inducedMap : Σs : Set (ℕ → β), s → α :=
  ⟨fun x => Set.Nonempty (⋂ n : ℕ, A (res x n)), fun x => x.property.some⟩

section Topology

protected def Antitone : Prop :=
  ∀ l : List β, ∀ a : β, A (a :: l) ⊆ A l

def ClosureAntitone [TopologicalSpace α] : Prop :=
  ∀ l : List β, ∀ a : β, closure (A (a :: l)) ⊆ A l

protected def Disjoint : Prop :=
  ∀ l : List β, Pairwise fun a b => Disjoint (A (a :: l)) (A (b :: l))

variable {A}

theorem map_mem (x : (inducedMap A).1) (n : ℕ) : (inducedMap A).2 x ∈ A (res x n) := by
  have := x.property.some_mem
  rw [mem_iInter] at this
  exact this n

protected theorem ClosureAntitone.antitone [TopologicalSpace α] (hA : ClosureAntitone A) :
    CantorScheme.Antitone A := fun l a => subset_closure.trans (hA l a)

protected theorem Antitone.closureAntitone [TopologicalSpace α] (hanti : CantorScheme.Antitone A)
    (hclosed : ∀ l, IsClosed (A l)) : ClosureAntitone A := fun _ _ =>
  (hclosed _).closure_eq.subset.trans (hanti _ _)

theorem Disjoint.map_injective (hA : CantorScheme.Disjoint A) : Injective (inducedMap A).2 := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  refine Subtype.coe_injective (res_injective ?_)
  dsimp
  ext n : 1
  induction' n with n ih; · simp
  simp only [res_succ, cons.injEq]
  refine ⟨?_, ih⟩
  contrapose hA
  simp only [CantorScheme.Disjoint, _root_.Pairwise, Ne, not_forall, exists_prop]
  refine ⟨res x n, _, _, hA, ?_⟩
  rw [not_disjoint_iff]
  refine ⟨(inducedMap A).2 ⟨x, hx⟩, ?_, ?_⟩
  · rw [← res_succ]
    apply map_mem
  rw [hxy, ih, ← res_succ]
  apply map_mem

end Topology

section Metric

variable [PseudoMetricSpace α]

def VanishingDiam : Prop :=
  ∀ x : ℕ → β, Tendsto (fun n : ℕ => EMetric.diam (A (res x n))) atTop (𝓝 0)

variable {A}

theorem VanishingDiam.dist_lt (hA : VanishingDiam A) (ε : ℝ) (ε_pos : 0 < ε) (x : ℕ → β) :
    ∃ n : ℕ, ∀ (y) (_ : y ∈ A (res x n)) (z) (_ : z ∈ A (res x n)), dist y z < ε := by
  specialize hA x
  rw [ENNReal.tendsto_atTop_zero] at hA
  cases' hA (ENNReal.ofReal (ε / 2)) (by
    simp only [gt_iff_lt, ENNReal.ofReal_pos]
    linarith) with n hn
  use n
  intro y hy z hz
  rw [← ENNReal.ofReal_lt_ofReal_iff ε_pos, ← edist_dist]
  apply lt_of_le_of_lt (EMetric.edist_le_diam_of_mem hy hz)
  apply lt_of_le_of_lt (hn _ (le_refl _))
  rw [ENNReal.ofReal_lt_ofReal_iff ε_pos]
  linarith

theorem VanishingDiam.map_continuous [TopologicalSpace β] [DiscreteTopology β]
    (hA : VanishingDiam A) : Continuous (inducedMap A).2 := by
  rw [Metric.continuous_iff']
  rintro ⟨x, hx⟩ ε ε_pos
  cases' hA.dist_lt _ ε_pos x with n hn
  rw [_root_.eventually_nhds_iff]
  refine ⟨(↑)⁻¹' cylinder x n, ?_, ?_, by simp⟩
  · rintro ⟨y, hy⟩ hyx
    rw [mem_preimage, Subtype.coe_mk, cylinder_eq_res, mem_setOf] at hyx
    apply hn
    · rw [← hyx]
      apply map_mem
    apply map_mem
  apply continuous_subtype_val.isOpen_preimage
  apply isOpen_cylinder

theorem ClosureAntitone.map_of_vanishingDiam [CompleteSpace α] (hdiam : VanishingDiam A)
    (hanti : ClosureAntitone A) (hnonempty : ∀ l, (A l).Nonempty) : (inducedMap A).1 = univ := by
  rw [eq_univ_iff_forall]
  intro x
  choose u hu using fun n => hnonempty (res x n)
  have umem : ∀ n m : ℕ, n ≤ m → u m ∈ A (res x n) := by
    have : Antitone fun n : ℕ => A (res x n) := by
      refine antitone_nat_of_succ_le ?_
      intro n
      apply hanti.antitone
    intro n m hnm
    exact this hnm (hu _)
  have : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε ε_pos
    cases' hdiam.dist_lt _ ε_pos x with n hn
    use n
    intro m₀ hm₀ m₁ hm₁
    apply hn <;> apply umem <;> assumption
  cases' cauchySeq_tendsto_of_complete this with y hy
  use y
  rw [mem_iInter]
  intro n
  apply hanti _ (x n)
  apply mem_closure_of_tendsto hy
  rw [eventually_atTop]
  exact ⟨n.succ, umem _⟩

end Metric

end CantorScheme
