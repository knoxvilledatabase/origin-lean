/-
Extracted from Topology/IndicatorConstPointwise.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pointwise convergence of indicator functions

In this file, we prove the equivalence of three different ways to phrase that the indicator
functions of sets converge pointwise.

## Main results

For `A` a set, `(Asᵢ)` an indexed collection of sets, under mild conditions, the following are
equivalent:

 (a) the indicator functions of `Asᵢ` tend to the indicator function of `A` pointwise;

 (b) for every `x`, we eventually have that `x ∈ Asᵢ` holds iff `x ∈ A` holds;

 (c) `Tendsto As _ <| Filter.pi (pure <| · ∈ A)`.

The results stating these in the case when the indicators take values in a Fréchet space are:
* `tendsto_indicator_const_iff_forall_eventually` is the equivalence (a) ↔ (b);
* `tendsto_indicator_const_iff_tendsto_pi_pure` is the equivalence (a) ↔ (c).

-/

open Filter Topology

variable {α : Type*} {A : Set α}

variable {β : Type*} [Zero β] [TopologicalSpace β]

variable {ι : Type*} (L : Filter ι) {As : ι → Set α}

lemma tendsto_ite {β : Type*} {p : ι → Prop} [DecidablePred p] {q : Prop} [Decidable q]
    {a b : β} {F G : Filter β}
    (haG : {a}ᶜ ∈ G) (hbF : {b}ᶜ ∈ F) (haF : principal {a} ≤ F) (hbG : principal {b} ≤ G) :
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) ↔ ∀ᶠ i in L, p i ↔ q := by
  constructor <;> intro h
  · by_cases hq : q
    · simp only [hq, ite_true] at h
      filter_upwards [mem_map.mp (h hbF)] with i hi
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        ite_eq_right_iff, not_forall, exists_prop] at hi
      tauto
    · simp only [hq, ite_false] at h
      filter_upwards [mem_map.mp (h haG)] with i hi
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        ite_eq_left_iff, not_forall, exists_prop] at hi
      tauto
  · have obs : (fun _ ↦ if q then a else b) =ᶠ[L] (fun i ↦ if p i then a else b) := by
      filter_upwards [h] with i hi
      simp only [hi]
    apply Tendsto.congr' obs
    by_cases hq : q
    · simp only [hq, ite_true]
      apply le_trans _ haF
      simp
    · simp only [hq, ite_false]
      apply le_trans _ hbG
      simp only [principal_singleton, le_pure_iff, mem_map, Set.mem_singleton_iff,
        Set.preimage_const_of_mem, univ_mem]

lemma tendsto_indicator_const_apply_iff_eventually' (b : β)
    (nhds_b : {0}ᶜ ∈ 𝓝 b) (nhds_o : {b}ᶜ ∈ 𝓝 0) (x : α) :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b) x) L (𝓝 (A.indicator (fun (_ : α) ↦ b) x))
      ↔ ∀ᶠ i in L, (x ∈ As i ↔ x ∈ A) := by
  classical
  have heart := @tendsto_ite ι L β (fun i ↦ x ∈ As i) _ (x ∈ A) _ b 0 (𝓝 b) (𝓝 (0 : β))
                nhds_o nhds_b ?_ ?_
  · convert heart
    by_cases hxA : x ∈ A <;> simp [hxA]
  · simp only [principal_singleton, le_def, mem_pure]
    exact fun s s_nhds ↦ mem_of_mem_nhds s_nhds
  · simp only [principal_singleton, le_def, mem_pure]
    exact fun s s_nhds ↦ mem_of_mem_nhds s_nhds

lemma tendsto_indicator_const_iff_forall_eventually'
    (b : β) (nhds_b : {0}ᶜ ∈ 𝓝 b) (nhds_o : {b}ᶜ ∈ 𝓝 0) :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ ∀ x, ∀ᶠ i in L, (x ∈ As i ↔ x ∈ A) := by
  simp_rw [tendsto_pi_nhds]
  apply forall_congr'
  exact tendsto_indicator_const_apply_iff_eventually' L b nhds_b nhds_o
