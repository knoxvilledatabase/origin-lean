/-
Extracted from Combinatorics/SimpleGraph/Extremal/TuranDensity.lean
Genuine: 7 of 9 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# Turán density

This file defines the **Turán density** of a simple graph.

## Main definitions

* `SimpleGraph.turanDensity H` is the **Turán density** of the simple graph `H`, defined as the
  limit of `extremalNumber n H / n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.tendsto_turanDensity` is the proof that `SimpleGraph.turanDensity` is well-defined.

* `SimpleGraph.isEquivalent_extremalNumber` is the proof that `extremalNumber n H` is
  asymptotically equivalent to `turanDensity H * n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.isContained_of_card_edgeFinset`: simple graphs on `n` vertices with at least
  `(turanDensity H + o(1)) * n ^ 2` edges contain `H`, for all sufficiently large `n`.
-/

open Asymptotics Filter Finset Fintype Topology

namespace SimpleGraph

variable {W : Type*}

lemma antitoneOn_extremalNumber_div_choose_two (H : SimpleGraph W) :
    AntitoneOn (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) (Set.Ici 2) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  conv_lhs =>
    enter [1, 1]
    rw [← Fintype.card_fin (n + 1)]
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith)),
    extremalNumber_le_iff_of_nonneg H (by positivity)]
  intro G _ h
  rw [mul_comm, ← mul_div_assoc, le_div_iff₀' (mod_cast Nat.choose_pos hn), Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_add_one, add_sub_cancel_right (n : ℝ) 1,
    mul_comm _ (n - 1 : ℝ), ← mul_div (n - 1 : ℝ), mul_comm _ (n / 2 : ℝ), mul_assoc,
    mul_comm (n - 1 : ℝ), ← mul_div (n + 1 : ℝ), mul_comm _ (n / 2 : ℝ), mul_assoc,
    mul_le_mul_iff_right₀ (by positivity), ← Nat.cast_pred (by positivity), ← Nat.cast_mul,
    ← Nat.cast_add_one, ← Nat.cast_mul, Nat.cast_le]
  conv_rhs =>
    rw [← Fintype.card_fin (n + 1), ← card_univ]
  -- double counting `(v, e) ↦ v ∉ e`
  apply card_nsmul_le_card_nsmul' (r := fun v e ↦ v ∉ e)
  -- counting `e`
  · intro e he
    simp_rw [← Sym2.mem_toFinset, bipartiteBelow, filter_not, filter_mem_eq_inter, univ_inter,
      ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin, card_toFinset_mem_edgeFinset ⟨e, he⟩,
      Nat.cast_id, Nat.reduceSubDiff, le_refl]
  -- counting `v`
  · intro v hv
    simpa [edgeFinset_deleteIncidenceSet_eq_filter]
      using card_edgeFinset_deleteIncidenceSet_le_extremalNumber h v

noncomputable def turanDensity (H : SimpleGraph W) :=
  limUnder atTop fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)

theorem isGLB_turanDensity (H : SimpleGraph W) :
    IsGLB { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } (turanDensity H) := by
  have h_bdd : BddBelow { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } := by
    refine ⟨0, fun x ⟨_, _, hx⟩ ↦ ?_⟩
    rw [← hx]
    positivity
  refine Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici ?_
    (antitoneOn_extremalNumber_div_choose_two H) h_bdd
  have h_tto := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (antitoneOn_extremalNumber_div_choose_two H) h_bdd
  rwa [← h_tto.limUnder_eq] at h_tto

theorem turanDensity_eq_csInf (H : SimpleGraph W) :
    turanDensity H = sInf { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } :=
  have h := isGLB_turanDensity H
  (h.csInf_eq h.nonempty).symm

theorem tendsto_turanDensity (H : SimpleGraph W) :
    Tendsto (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 (turanDensity H)) := by
  have h_tendsto := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (antitoneOn_extremalNumber_div_choose_two H) (isGLB_turanDensity H).bddBelow
  rwa [turanDensity, h_tendsto.limUnder_eq]

-- DISSOLVED: isEquivalent_extremalNumber

open Classical in

noncomputable abbrev turanDensityConst (H : SimpleGraph W) (ε : ℝ) :=
  if h : ε > 0 then
    Nat.find <| eventually_atTop.mp <| eventually_isContained_of_card_edgeFinset H h
  else 0

open Classical in

theorem isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε)
    {V : Type*} [Fintype V] (h_verts : card V ≥ turanDensityConst H ε)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset ≥ (turanDensity H + ε) * (card V).choose 2 → H ⊑ G := by
  rw [(G.overFinIso rfl).card_edgeFinset_eq, isContained_congr Iso.refl (G.overFinIso rfl)]
  apply Nat.find_spec <| eventually_atTop.mp <| eventually_isContained_of_card_edgeFinset H hε_pos
  simpa only [turanDensityConst, hε_pos, ↓reduceDIte] using h_verts

end SimpleGraph
