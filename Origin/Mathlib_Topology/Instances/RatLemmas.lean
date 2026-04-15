/-
Extracted from Topology/Instances/RatLemmas.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Additional lemmas about the topology on rational numbers

The structure of a metric space on `ℚ` (`Rat.MetricSpace`) is introduced elsewhere, induced from
`ℝ`. In this file we prove some properties of this topological space and its one-point
compactification.

## Main statements

- `Rat.TotallyDisconnectedSpace`: `ℚ` is a totally disconnected space;

- `Rat.not_countably_generated_nhds_infty_opc`: the filter of neighbourhoods of infinity in
  `OnePoint ℚ` is not countably generated.

## Notation

- `ℚ∞` is used as a local notation for `OnePoint ℚ`
-/

open Set Metric Filter TopologicalSpace

open Topology OnePoint

local notation "ℚ∞" => OnePoint ℚ

namespace Rat

variable {p : ℚ} {s : Set ℚ}

theorem interior_compact_eq_empty (hs : IsCompact s) : interior s = ∅ :=
  isDenseEmbedding_coe_real.isDenseInducing.interior_compact_eq_empty dense_irrational hs

theorem dense_compl_compact (hs : IsCompact s) : Dense sᶜ :=
  interior_eq_empty_iff_dense_compl.1 (interior_compact_eq_empty hs)

-- INSTANCE (free from Core): cocompact_inf_nhds_neBot

theorem not_countably_generated_cocompact : ¬IsCountablyGenerated (cocompact ℚ) := by
  intro H
  rcases exists_seq_tendsto (cocompact ℚ ⊓ 𝓝 0) with ⟨x, hx⟩
  rw [tendsto_inf] at hx; rcases hx with ⟨hxc, hx0⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x n ∉ insert (0 : ℚ) (range x) :=
    (hxc.eventually hx0.isCompact_insert_range.compl_mem_cocompact).exists
  exact hn (Or.inr ⟨n, rfl⟩)

theorem not_countably_generated_nhds_infty_opc : ¬IsCountablyGenerated (𝓝 (∞ : ℚ∞)) := by
  intro
  have : IsCountablyGenerated (comap (OnePoint.some : ℚ → ℚ∞) (𝓝 ∞)) := by infer_instance
  rw [OnePoint.comap_coe_nhds_infty, coclosedCompact_eq_cocompact] at this
  exact not_countably_generated_cocompact this

theorem not_firstCountableTopology_opc : ¬FirstCountableTopology ℚ∞ := by
  intro
  exact not_countably_generated_nhds_infty_opc inferInstance

theorem not_secondCountableTopology_opc : ¬SecondCountableTopology ℚ∞ := by
  intro
  exact not_firstCountableTopology_opc inferInstance

-- INSTANCE (free from Core): :

end Rat
