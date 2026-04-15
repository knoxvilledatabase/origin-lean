/-
Extracted from Topology/MetricSpace/Sequences.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Sequential compacts in metric spaces

In this file we prove 2 versions of Bolzano-Weierstrass theorem for proper metric spaces.
-/

open Filter Bornology Metric

open scoped Topology

variable {X : Type*} [PseudoMetricSpace X]

nonrec theorem SeqCompact.lebesgue_number_lemma_of_metric {ι : Sort*} {c : ι → Set X} {s : Set X}
    (hs : IsSeqCompact s) (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
    ∃ δ > 0, ∀ a ∈ s, ∃ i, ball a δ ⊆ c i :=
  lebesgue_number_lemma_of_metric hs.isCompact hc₁ hc₂

variable [ProperSpace X] {s : Set X}

theorem tendsto_subseq_of_frequently_bounded (hs : IsBounded s) {x : ℕ → X}
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  have hcs : IsSeqCompact (closure s) := hs.isCompact_closure.isSeqCompact
  have hu' : ∃ᶠ n in atTop, x n ∈ closure s := hx.mono fun _n hn => subset_closure hn
  hcs.subseq_of_frequently_in hu'

theorem tendsto_subseq_of_bounded (hs : IsBounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  tendsto_subseq_of_frequently_bounded hs <| Frequently.of_forall hx
